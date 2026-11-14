-- Prove2me | solution 1 for CalibratedMA.Randomized.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:19:05.945012+00:00
-- url     : https://prove2.me/submissions/5ff89bcf-9917-498c-9706-2cfa442369f4

import Theorems.Thm_CalibratedMA_Randomized_lemma_3_2



open MeasureTheory

namespace CalibratedMA.Randomized.VariationAlgebra

/-- Extend a finite coefficient sequence by zero at its right endpoint. -/
def zeroExtend (M : ℕ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < M then q j else 0

/-- The preceding coefficient, with zero at the left boundary. -/
def previous (M : ℕ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else zeroExtend M q (j - 1)

/-- Discrete summation by parts, with both boundary coefficients set to zero. -/
lemma summation_by_parts (M : ℕ) (a q : ℕ → ℝ) :
    (∑ j ∈ Finset.range M, (a j - a (j + 1)) * q j) =
      ∑ j ∈ Finset.range (M + 1), a j * (zeroExtend M q j - previous M q j) := by
  have hleft : (∑ j ∈ Finset.range (M + 1), a j * zeroExtend M q j) =
      ∑ j ∈ Finset.range M, a j * q j := by
    rw [Finset.sum_range_succ]
    simp only [zeroExtend, lt_self_iff_false, if_false, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [hj, if_true]
  have hright : (∑ j ∈ Finset.range (M + 1), a j * previous M q j) =
      ∑ j ∈ Finset.range M, a (j + 1) * q j := by
    rw [Finset.sum_range_succ']
    simp only [previous, if_true, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    simp [zeroExtend, hjM]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hleft, hright]
  simp_rw [sub_mul, Finset.sum_sub_distrib]

/-- Bounded tests cannot exceed the total variation of the coefficient sequence. -/
lemma abs_sum_le_variation (M : ℕ) (a q : ℕ → ℝ)
    (ha : ∀ j ≤ M, |a j| ≤ 1) :
    |∑ j ∈ Finset.range M, (a j - a (j + 1)) * q j| ≤
      ∑ j ∈ Finset.range (M + 1), |zeroExtend M q j - previous M q j| := by
  rw [summation_by_parts]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (ha j (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (abs_nonneg (zeroExtend M q j - previous M q j))

lemma abs_signVal_le_one {M : ℕ} (σ : Fin (M + 1) → Bool) (j : ℕ) :
    |signVal σ j| ≤ 1 := by
  unfold signVal
  split_ifs <;> norm_num

/-- Choosing each test value to be the sign of its coefficient attains total variation. -/
lemma exists_sign_attaining_variation (M : ℕ) (q : ℕ → ℝ) :
    ∃ σ : Fin (M + 1) → Bool,
      |∑ j ∈ Finset.range M, (signVal σ j - signVal σ (j + 1)) * q j| =
        ∑ j ∈ Finset.range (M + 1), |zeroExtend M q j - previous M q j| := by
  classical
  let σ : Fin (M + 1) → Bool :=
    fun j => decide (0 ≤ zeroExtend M q j - previous M q j)
  refine ⟨σ, ?_⟩
  rw [summation_by_parts]
  have hterm : ∀ j ∈ Finset.range (M + 1),
      signVal σ j * (zeroExtend M q j - previous M q j) =
        |zeroExtend M q j - previous M q j| := by
    intro j hj
    have hjM : j < M + 1 := Finset.mem_range.mp hj
    by_cases hd : 0 ≤ zeroExtend M q j - previous M q j
    · have hσ : σ ⟨j, hjM⟩ = true := decide_eq_true hd
      simp [signVal, hjM, hσ, abs_of_nonneg hd]
    · have hσ : σ ⟨j, hjM⟩ = false := decide_eq_false hd
      simp [signVal, hjM, hσ, abs_of_neg (lt_of_not_ge hd)]
  rw [Finset.sum_congr rfl hterm, abs_of_nonneg]
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The supremum over Boolean sign assignments is exactly total variation. -/
lemma sign_sup_eq_variation (M : ℕ) (q : ℕ → ℝ) :
    (⨆ σ : Fin (M + 1) → Bool,
      |∑ j ∈ Finset.range M, (signVal σ j - signVal σ (j + 1)) * q j|) =
        ∑ j ∈ Finset.range (M + 1), |zeroExtend M q j - previous M q j| := by
  let f : (Fin (M + 1) → Bool) → ℝ := fun σ =>
    |∑ j ∈ Finset.range M, (signVal σ j - signVal σ (j + 1)) * q j|
  have hb : ∀ σ, f σ ≤
      ∑ j ∈ Finset.range (M + 1), |zeroExtend M q j - previous M q j| := by
    intro σ
    exact abs_sum_le_variation M (signVal σ) q (fun j _ => abs_signVal_le_one σ j)
  have hbounded : BddAbove (Set.range f) := by
    refine ⟨∑ j ∈ Finset.range (M + 1), |zeroExtend M q j - previous M q j|, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact hb σ
  apply le_antisymm
  · exact ciSup_le hb
  · obtain ⟨σ, hσ⟩ := exists_sign_attaining_variation M q
    exact hσ ▸ le_ciSup hbounded σ

/-- The algebraic total-variation formula for the mission's `RoundErr` definition. -/
lemma roundErr_eq_variation (ν : Measure ℝ) (M : ℕ) (γ : ℕ → ℝ) :
    RoundErr ν M γ =
      ∑ j ∈ Finset.range (M + 1),
        |zeroExtend M (qj ν γ) j - previous M (qj ν γ) j| :=
  sign_sup_eq_variation M (qj ν γ)

end CalibratedMA.Randomized.VariationAlgebra


open MeasureTheory

namespace CalibratedMA.Randomized.VariationIntegrability

lemma rj_nonneg (γ : ℕ → ℝ) (j : ℕ) (s : ℝ) : 0 ≤ rj γ j s := by
  unfold rj
  split_ifs with hs
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hs.1.le) (sub_nonneg.mpr hs.2.le))
      (sub_nonneg.mpr (hs.1.trans hs.2).le)
  · exact le_refl 0

lemma measurable_rj (γ : ℕ → ℝ) (j : ℕ) : Measurable (rj γ j) := by
  unfold rj
  apply Measurable.ite (show MeasurableSet (Set.Ioo (γ j) (γ (j + 1))) from measurableSet_Ioo)
  · fun_prop
  · exact measurable_const

lemma rj_le_width (γ : ℕ → ℝ) (j : ℕ) (hγ : γ j < γ (j + 1)) (s : ℝ) :
    rj γ j s ≤ γ (j + 1) - γ j := by
  unfold rj
  split_ifs with hs
  · apply (div_le_iff₀ (sub_pos.mpr hγ)).2
    exact mul_le_mul (sub_le_sub_right hs.2.le _) (sub_le_sub_left hs.1.le _)
      (sub_nonneg.mpr hs.2.le) (sub_nonneg.mpr hγ.le)
  · exact sub_nonneg.mpr hγ.le

lemma integrable_rj_of_lt (ν : Measure ℝ) [IsFiniteMeasure ν] (γ : ℕ → ℝ) (j : ℕ)
    (hγ : γ j < γ (j + 1)) : Integrable (rj γ j) ν := by
  apply (integrable_const (γ (j + 1) - γ j)).mono_nonneg
    (measurable_rj γ j).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (rj_nonneg γ j)
  · exact Filter.Eventually.of_forall (rj_le_width γ j hγ)

lemma integrable_rj (ν : Measure ℝ) [IsFiniteMeasure ν] (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (j : ℕ) (hj : j < M) : Integrable (rj γ j) ν :=
  integrable_rj_of_lt ν γ j (hΓ.2.2.1 j hj)

lemma qj_nonneg (ν : Measure ℝ) (γ : ℕ → ℝ) (j : ℕ) : 0 ≤ qj ν γ j := by
  exact integral_nonneg (rj_nonneg γ j)

lemma variation_sum_endpoints (M : ℕ) (hM : 0 < M) (q : ℕ → ℝ)
    (hzero : 0 ≤ q 0) (hlast : 0 ≤ q (M - 1)) :
    let qzero : ℕ → ℝ := fun j => if j < M then q j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else qzero (j - 1)
    (∑ j ∈ Finset.range (M + 1), |qzero j - qprev j|) =
      q 0 + q (M - 1) + ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| := by
  let v : ℕ → ℝ := fun j =>
    |(if j < M then q j else 0) - (if j = 0 then 0 else if j - 1 < M then q (j - 1) else 0)|
  change (∑ j ∈ Finset.range (M + 1), v j) = _
  have hvzero : v 0 = q 0 := by simp [v, hM, abs_of_nonneg hzero]
  have hvlast : v M = q (M - 1) := by
    have hpred : M - 1 < M := by omega
    simp [v, Nat.ne_of_gt hM, hpred, abs_of_nonneg hlast]
  have hmiddle : (∑ j ∈ Finset.Ico 1 M, v j) =
      ∑ j ∈ Finset.Ico 1 M, |q j - q (j - 1)| := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjM⟩ := Finset.mem_Ico.mp hj
    have hjne : j ≠ 0 := by omega
    have hpred : j - 1 < M := by omega
    simp [v, hjM, hjne, hpred]
  rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hM, hvzero, hvlast, hmiddle]
  ring

lemma qj_variation_sum_endpoints (ν : Measure ℝ) (γ : ℕ → ℝ) (M : ℕ) (hM : 0 < M) :
    let q : ℕ → ℝ := fun j => if j < M then qj ν γ j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else q (j - 1)
    (∑ j ∈ Finset.range (M + 1), |q j - qprev j|) =
      qj ν γ 0 + qj ν γ (M - 1) +
        ∑ j ∈ Finset.Ico 1 M, |qj ν γ j - qj ν γ (j - 1)| :=
  variation_sum_endpoints M hM (qj ν γ) (qj_nonneg ν γ 0) (qj_nonneg ν γ (M - 1))

end CalibratedMA.Randomized.VariationIntegrability


open MeasureTheory

namespace CalibratedMA.Randomized.VariationPointwise

/-- Clamping has no effect on an admissible score. -/
lemma clamp01_eq_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    clamp01 s = s := by
  simp only [clamp01, min_eq_right hs.2, max_eq_right hs.1]

/-- The selected interval contains the score, including at both boundary points. -/
lemma roundIndex_bounds (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    roundIndex M γ s < M ∧
      γ (roundIndex M γ s) ≤ s ∧ s ≤ γ (roundIndex M γ s + 1) := by
  classical
  rcases hΓ with ⟨hzero, hone, _, _⟩
  have hM : 0 < M := by
    by_contra h
    have : M = 0 := by omega
    subst M
    linarith
  have hclamp : clamp01 s = s := clamp01_eq_of_mem hs
  let F := (Finset.range M).filter (fun j => γ j ≤ s)
  have hF : F.Nonempty := by
    refine ⟨0, ?_⟩
    simp [F, hM, hzero, hs.1]
  have hjmem : F.sup id ∈ F := by
    simpa only [Set.image_id, Finset.mem_coe] using
      (Finset.sup_mem_of_nonempty (f := id) hF)
  have hj : F.sup id < M ∧ γ (F.sup id) ≤ s := by
    simpa only [F, Finset.mem_filter, Finset.mem_range] using hjmem
  have hright : s ≤ γ (F.sup id + 1) := by
    by_cases hlast : F.sup id + 1 = M
    · simpa only [hlast, hone] using hs.2
    · by_contra h
      have hnext : F.sup id + 1 ∈ F := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), (lt_of_not_ge h).le⟩
      have hle : F.sup id + 1 ≤ F.sup id := Finset.le_sup (f := id) hnext
      omega
  simpa only [roundIndex, hclamp, F] using ⟨hj.1, hj.2, hright⟩

lemma grid_strictMonoOn (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) :
    StrictMonoOn γ (Set.Iic M) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact hΓ.2.2.1 j hj

/-- The interval contribution vanishes at its boundary, so the polynomial formula
extends from the open interval to the closed interval. -/
lemma rj_eq_of_mem (γ : ℕ → ℝ) (j : ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc (γ j) (γ (j + 1))) :
    rj γ j s = (s - γ j) * (γ (j + 1) - s) / (γ (j + 1) - γ j) := by
  rcases hs.1.eq_or_lt with heq | hlo
  · rw [← heq]
    simp [rj]
  rcases hs.2.eq_or_lt with heq | hhi
  · rw [heq]
    simp [rj]
  · simp [rj, hlo, hhi]

/-- A score in one closed partition interval has zero contribution in every other
interval; this includes common endpoints because `rj` uses an open-interval indicator. -/
lemma rj_eq_zero_of_other (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (j k : ℕ) (hj : j < M) (hk : k < M) (hne : j ≠ k) (s : ℝ)
    (hs : s ∈ Set.Icc (γ k) (γ (k + 1))) :
    rj γ j s = 0 := by
  have hmono := (grid_strictMonoOn K M γ hΓ).monotoneOn
  unfold rj
  split_ifs with hi
  · rcases lt_or_gt_of_ne hne with hjk | hkj
    · have he : γ (j + 1) ≤ γ k :=
        hmono (show j + 1 ≤ M by omega) (show k ≤ M by omega) (by omega)
      linarith [hi.2, hs.1]
    · have he : γ (k + 1) ≤ γ j :=
        hmono (show k + 1 ≤ M by omega) (show j ≤ M by omega) (by omega)
      linarith [hi.1, hs.2]
  · rfl

/-- The conditional rounding residual is the sum of the signed interval contributions. -/
lemma rounding_residual_pointwise (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (h : ℝ → ℝ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∫ p, h p * (s - p) ∂(roundMeasure M γ s)) =
      ∑ j ∈ Finset.range M, (h (γ j) - h (γ (j + 1))) * rj γ j s := by
  classical
  let k := roundIndex M γ s
  obtain ⟨hk, hks⟩ := roundIndex_bounds K M γ hΓ s hs
  change k < M at hk
  change s ∈ Set.Icc (γ k) (γ (k + 1)) at hks
  have hf := (lemma_3_2 K M γ hΓ (fun p => h p * (s - p))).1 k hk s hks
  change (∫ p, h p * (s - p) ∂(roundMeasure M γ s)) = _ at hf
  have hden : γ (k + 1) - γ k ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hΓ.2.2.1 k hk))
  rw [Finset.sum_eq_single k]
  · rw [hf, rj_eq_of_mem γ k s hks]
    field_simp [hden]
    ring
  · intro j hj hne
    rw [rj_eq_zero_of_other K M γ hΓ j k (Finset.mem_range.mp hj) hk hne s hks]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim

end CalibratedMA.Randomized.VariationPointwise



open MeasureTheory

namespace CalibratedMA.Randomized.VariationAssembly

lemma extend_grid (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ)
    (a : ℕ → ℝ) : ∃ h : ℝ → ℝ, ∀ j ≤ M, h (γ j) = a j := by
  classical
  have hmono : StrictMonoOn γ (Set.Iic M) :=
    strictMonoOn_Iic_of_lt_succ (fun j hj => hΓ.2.2.1 j hj)
  have hinj : Function.Injective (fun j : Fin (M + 1) => γ j) := by
    intro i j hij
    apply Fin.ext
    exact hmono.injOn (show (i : ℕ) ≤ M by omega) (show (j : ℕ) ≤ M by omega) hij
  refine ⟨Function.extend (fun j : Fin (M + 1) => γ j) (fun j => a j)
    (fun _ => 0), ?_⟩
  intro j hj
  exact hinj.extend_apply (fun j => a j) (fun _ => 0) ⟨j, by omega⟩

lemma outer_integral_of_pointwise (M : ℕ) (γ : ℕ → ℝ) (ν : Measure ℝ)
    (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) (h : ℝ → ℝ)
    (hr : ∀ j < M, Integrable (rj γ j) ν)
    (hp : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ p, h p * (s - p) ∂roundMeasure M γ s) =
        ∑ j ∈ Finset.range M, (h (γ j) - h (γ (j + 1))) * rj γ j s) :
    (∫ s, (∫ p, h p * (s - p) ∂roundMeasure M γ s) ∂ν) =
      ∑ j ∈ Finset.range M, (h (γ j) - h (γ (j + 1))) * qj ν γ j := by
  have hae : ∀ᵐ s ∂ν, s ∈ Set.Icc (0 : ℝ) 1 := by
    exact ae_iff.mpr hν
  rw [integral_congr_ae (hae.mono (fun s hs => hp s hs))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact integral_const_mul _ _
  · intro j hj
    exact (hr j (Finset.mem_range.mp hj)).const_mul _

lemma rounding_residual_integral (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) (h : ℝ → ℝ) :
    (∫ s, (∫ p, h p * (s - p) ∂roundMeasure M γ s) ∂ν) =
      ∑ j ∈ Finset.range M, (h (γ j) - h (γ (j + 1))) * qj ν γ j :=
  outer_integral_of_pointwise M γ ν hν h
    (VariationIntegrability.integrable_rj ν K M γ hΓ)
    (VariationPointwise.rounding_residual_pointwise K M γ hΓ h)

lemma roundErr_isLUB (K M : ℕ) (γ : ℕ → ℝ)
    (hΓ : IsGridPartition K M γ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    IsLUB {v : ℝ | ∃ h : ℝ → ℝ, (∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) ∧
      v = |∫ s, (∫ p, h p * (s - p) ∂roundMeasure M γ s) ∂ν|}
      (RoundErr ν M γ) := by
  have hupper : ∀ v ∈ {v : ℝ | ∃ h : ℝ → ℝ,
      (∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) ∧
      v = |∫ s, (∫ p, h p * (s - p) ∂roundMeasure M γ s) ∂ν|},
      v ≤ RoundErr ν M γ := by
    rintro v ⟨h, hh, rfl⟩
    rw [rounding_residual_integral K M γ hΓ ν hν h,
      VariationAlgebra.roundErr_eq_variation]
    apply VariationAlgebra.abs_sum_le_variation
    intro j hj
    exact abs_le.mpr (hh j hj)
  have hattain : ∃ h : ℝ → ℝ, (∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) ∧
      RoundErr ν M γ = |∫ s, (∫ p, h p * (s - p) ∂roundMeasure M γ s) ∂ν| := by
    obtain ⟨σ, hσ⟩ := VariationAlgebra.exists_sign_attaining_variation M (qj ν γ)
    obtain ⟨h, hh⟩ := extend_grid K M γ hΓ (signVal σ)
    refine ⟨h, ?_, ?_⟩
    · intro j hj
      rw [hh j hj]
      exact abs_le.mp (VariationAlgebra.abs_signVal_le_one σ j)
    · rw [rounding_residual_integral K M γ hΓ ν hν h,
        VariationAlgebra.roundErr_eq_variation, ← hσ]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjM := Finset.mem_range.mp hj
      rw [hh j (by omega), hh (j + 1) (by omega)]
  exact ⟨hupper, fun b hb => hb hattain⟩

end CalibratedMA.Randomized.VariationAssembly

open CalibratedMA.Randomized

theorem solution (K M : ℕ) (γ : ℕ → ℝ) (hΓ : IsGridPartition K M γ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    let q : ℕ → ℝ := fun j => if j < M then qj ν γ j else 0
    let qprev : ℕ → ℝ := fun j => if j = 0 then 0 else q (j - 1)
    IsLUB {v : ℝ | ∃ h : ℝ → ℝ, (∀ j ≤ M, h (γ j) ∈ Set.Icc (-1 : ℝ) 1) ∧
        v = |∫ s, (∫ p, h p * (s - p) ∂(roundMeasure M γ s)) ∂ν|} (RoundErr ν M γ) ∧
    RoundErr ν M γ = qj ν γ 0 + qj ν γ (M - 1) +
        ∑ j ∈ Finset.Ico 1 M, |qj ν γ j - qj ν γ (j - 1)| ∧
    RoundErr ν M γ = ∑ j ∈ Finset.range (M + 1), |q j - qprev j|  := by
  dsimp only
  have hM : 0 < M := by
    by_contra h
    have hM0 : M = 0 := by omega
    have hzero := hΓ.1
    have hone := hΓ.2.1
    rw [hM0] at hone
    linarith
  refine ⟨VariationAssembly.roundErr_isLUB K M γ hΓ ν hν, ?_, ?_⟩
  · exact (VariationAlgebra.roundErr_eq_variation ν M γ).trans
      (VariationIntegrability.qj_variation_sum_endpoints ν γ M hM)
  · exact VariationAlgebra.roundErr_eq_variation ν M γ


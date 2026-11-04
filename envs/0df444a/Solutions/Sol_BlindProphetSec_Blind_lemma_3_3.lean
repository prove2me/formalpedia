-- Prove2me | solution 1 for BlindProphetSec.Blind.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:32:51.698577+00:00
-- url     : https://prove2.me/submissions/f7c9f01f-270f-4360-b7e5-cf645e38ef43

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

open MeasureTheory Filter Topology

namespace BPSLem33

open BlindProphetSec.Blind

/-- The distribution function of an atomless probability measure on `ℝ` is continuous. -/
lemma cdf_cont (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    Continuous fun x => (ν (Set.Iic x)).toReal := by
  have e : (fun x => (ν (Set.Iic x)).toReal) = ProbabilityTheory.cdf ν := by
    funext x; rw [ProbabilityTheory.cdf_eq_real]; rfl
  rw [e, continuous_iff_continuousAt]
  intro x
  set f := ProbabilityTheory.cdf ν
  rw [f.mono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  apply le_antisymm (f.mono.leftLim_le le_rfl)
  have h := f.measure_singleton x
  rw [ProbabilityTheory.measure_cdf, measure_singleton] at h
  have := ENNReal.ofReal_eq_zero.mp h.symm
  linarith

lemma fmax_eq {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (x : ℝ) :
    Fmax μ x = ∏ i, (μ i (Set.Iic x)).toReal := by
  unfold Fmax
  have : {v : Fin n → ℝ | ∀ i, v i ≤ x} = Set.univ.pi (fun _ => Set.Iic x) := by
    ext v; simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [this, Measure.pi_pi, ENNReal.toReal_prod]

lemma fmax_cont {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] : Continuous (Fmax μ) := by
  have : Fmax μ = fun x => ∏ i, (μ i (Set.Iic x)).toReal := funext (fmax_eq μ)
  rw [this]
  exact continuous_finsetProd _ fun i _ => cdf_cont (μ i)

lemma fmax_mono {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    Monotone (Fmax μ) := by
  intro x y h
  rw [fmax_eq, fmax_eq]
  exact Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg)
    (fun i _ => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr h)))

lemma toReal_le_one' (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : Set ℝ) : (ν s).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

lemma fmax_le_one {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (x : ℝ) :
    Fmax μ x ≤ 1 := by
  rw [fmax_eq]
  exact Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) (fun i _ => toReal_le_one' _ _)

lemma fmax_neg {n : ℕ} (hn : 0 < n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hnn : ∀ i, μ i (Set.Iio 0) = 0) (x : ℝ) (hx : x < 0) : Fmax μ x = 0 := by
  rw [fmax_eq]
  apply Finset.prod_eq_zero (i := ⟨0, hn⟩) (Finset.mem_univ _)
  rw [measure_mono_null (Set.Iic_subset_Iio.mpr hx) (hnn _)]
  simp

lemma fmax_tendsto {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    Tendsto (Fmax μ) atTop (𝓝 1) := by
  have : Fmax μ = fun x => ∏ i, (μ i (Set.Iic x)).toReal := funext (fmax_eq μ)
  rw [this]
  have : (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
  rw [this]
  apply tendsto_finsetProd
  intro i _
  have h1 := tendsto_measure_Iic_atTop (μ i)
  rw [measure_univ] at h1
  have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
  rw [ENNReal.toReal_one] at this
  exact this

/-- Column identity: `∏_i P(F_max(V_i) ≤ β) = β` for `β ∈ [0, 1]` (continuous laws). -/
lemma col {n : ℕ} (hn : 0 < n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (hnn : ∀ i, μ i (Set.Iio 0) = 0) (β : ℝ) (h0 : 0 ≤ β)
    (h1 : β ≤ 1) : ∏ i, (μ i {x | Fmax μ x ≤ β}).toReal = β := by
  rcases eq_or_lt_of_le h1 with hb | hb
  · subst hb
    have : {x | Fmax μ x ≤ 1} = Set.univ := by
      ext x; simp [fmax_le_one]
    simp [this]
  · set S := {x | Fmax μ x ≤ β} with hS
    obtain ⟨R, hR⟩ : ∃ R, β < Fmax μ R :=
      ((fmax_tendsto μ).eventually (lt_mem_nhds hb)).exists
    have hSc : IsClosed S := isClosed_le (fmax_cont μ) continuous_const
    have hSne : (-1 : ℝ) ∈ S := by
      show Fmax μ (-1) ≤ β
      rw [fmax_neg hn μ hnn _ (by norm_num)]; exact h0
    have hSbdd : ∀ x ∈ S, x ≤ R := by
      intro x hx
      by_contra h
      push Not at h
      have := fmax_mono μ h.le
      have hx' : Fmax μ x ≤ β := hx
      linarith
    have hbdd : BddAbove S := ⟨R, hSbdd⟩
    set s := sSup S
    have hs : s ∈ S := hSc.csSup_mem ⟨-1, hSne⟩ hbdd
    have hSeq : S = Set.Iic s := by
      ext x
      constructor
      · intro hx; exact le_csSup hbdd hx
      · intro hx; exact le_trans (fmax_mono μ hx) hs
    have hsR : s ≤ R := hSbdd s hs
    obtain ⟨y, hy, hfy⟩ : β ∈ Fmax μ '' Set.Icc s R :=
      intermediate_value_Icc hsR (fmax_cont μ).continuousOn ⟨hs, hR.le⟩
    have hyS : y ∈ S := le_of_eq hfy
    have hys : y = s := le_antisymm (le_csSup hbdd hyS) hy.1
    rw [hSeq, ← fmax_eq, ← hys, hfy]

/-- Independence: `P(V_{σ j} ∈ S j ∀ j) = ∏_j μ_{σ j}(S j)`. -/
lemma box_prob' {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (σ : Equiv.Perm (Fin n)) (S : Fin n → Set ℝ) :
    ((Measure.pi μ) {v | ∀ j, v (σ j) ∈ S j}).toReal = ∏ j, (μ (σ j) (S j)).toReal := by
  have hset : {v : Fin n → ℝ | ∀ j, v (σ j) ∈ S j} = Set.univ.pi (fun p => S (σ.symm p)) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h p
      have := h (σ.symm p)
      simpa using this
    · intro h j
      have := h (σ j)
      simpa using this
  rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
  conv_lhs => rw [← Equiv.prod_comp σ]
  simp

/-- Each fiber `{σ | σ j = i}` has `n!/n` elements. -/
lemma fiber_card {n : ℕ} (j i : Fin n) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i)).card : ℝ) * n = n.factorial := by
  classical
  have heq : ∀ i i' : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i')).card := by
    intro i i'
    apply Finset.card_bij (fun σ _ => Equiv.swap i i' * σ)
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
    · intro a _ b _ h
      exact mul_left_cancel h
    · intro τ hτ
      refine ⟨Equiv.swap i i' * τ, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        rw [Equiv.Perm.mul_apply, hτ, Equiv.swap_apply_right]
      · rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) => σ j)
    (s := Finset.univ) (t := Finset.univ) (by intro σ _; simp)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Finset.sum_congr rfl (fun i' _ => heq i' i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  have : (n.factorial : ℝ) = (n : ℝ) * (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => σ j = i)).card := by exact_mod_cast hsum
  rw [this]; ring

end BPSLem33

open BlindProphetSec.Blind BPSLem33 in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (hnn : ∀ i, μ i (Set.Iio 0) = 0)
    (α : Fin n → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), (1 - α j) ≤
        probVS μ (fun v σ => stopLE (levelAcc μ α v σ) k) ∧
      probVS μ (fun v σ => stopLE (levelAcc μ α v σ) k) ≤
        1 - (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), α j) ^ ((1 : ℝ) / n) := by
  classical
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfacR : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  set Pk := Finset.univ.filter (fun j : Fin n => j.val < k) with hPk
  -- rejection sets and the matrix `x i j = P(F_max(V_i) ≤ α_j)`
  let S : Fin n → Set ℝ := fun j => {x | Fmax μ x ≤ α j}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (isClosed_le (fmax_cont μ) continuous_const).measurableSet
  let x : Fin n → Fin n → ℝ := fun i j => (μ i (S j)).toReal
  have hx0 : ∀ i j, 0 ≤ x i j := fun i j => ENNReal.toReal_nonneg
  have hcol : ∀ j, ∏ i, x i j = α j := fun j => col hn μ hnn (α j) (hα j).1 (hα j).2
  let Y : Equiv.Perm (Fin n) → ℝ := fun σ => ∏ j ∈ Pk, x (σ j) j
  have hY0 : ∀ σ, 0 ≤ Y σ := fun σ => Finset.prod_nonneg fun j _ => hx0 _ _
  -- the event `T ≤ k` for a fixed order
  let E : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ =>
    {v | stopLE (levelAcc μ α v σ) k}
  have hmeasF : Measurable (Fmax μ) := (fmax_cont μ).measurable
  have hEm : ∀ σ, MeasurableSet (E σ) := by
    intro σ
    have : E σ = ⋃ j ∈ Pk, {v : Fin n → ℝ | α j < Fmax μ (v (σ j))} := by
      ext v; simp [E, stopLE, levelAcc, hPk]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun j _ =>
      measurableSet_lt measurable_const (hmeasF.comp (measurable_pi_apply _))
  have hPE : ∀ σ, ((Measure.pi μ) (E σ)).toReal = 1 - Y σ := by
    intro σ
    have hc : (E σ)ᶜ = {v | ∀ j, v (σ j) ∈ (if j.val < k then S j else Set.univ)} := by
      ext v
      simp only [E, stopLE, levelAcc, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and,
        not_lt]
      constructor
      · intro h j
        split_ifs with hj
        · exact h j hj
        · trivial
      · intro h j hj
        have := h j
        rw [if_pos hj] at this
        exact this
    have hEc : (E σ) = ({v | ∀ j, v (σ j) ∈ (if j.val < k then S j else Set.univ)})ᶜ := by
      rw [← hc, compl_compl]
    have hbm : MeasurableSet {v : Fin n → ℝ | ∀ j, v (σ j) ∈ (if j.val < k then S j else Set.univ)} := by
      rw [← hc]; exact (hEm σ).compl
    rw [hEc, prob_compl_eq_one_sub hbm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      box_prob']
    simp only [ENNReal.toReal_one]
    congr 1
    have e : ∀ j, (μ (σ j) (if j.val < k then S j else Set.univ)).toReal =
        if j ∈ Pk then x (σ j) j else 1 := by
      intro j
      by_cases hj : j.val < k
      · simp [hj, hPk, x]
      · simp [hj, hPk]
    simp_rw [e]
    rw [Finset.prod_ite_mem]
    simp [Y]
  have hprob : probVS μ (fun v σ => stopLE (levelAcc μ α v σ) k) =
      1 / (n.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin n), (1 - Y σ) := by
    unfold probVS
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact hPE σ
  -- fiber count
  have hfib : ∀ j i : Fin n,
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i)).card : ℝ) =
        n.factorial / n := by
    intro j i
    rw [eq_div_iff hnR.ne']
    exact fiber_card j i
  constructor
  · ------------------------------------------------------------------ lower bound
    -- acceptance sets `G j = {∃ i, α_j < F_max(V_i)}`
    let G : Fin n → Set (Fin n → ℝ) := fun j => {v | ∃ i, α j < Fmax μ (v i)}
    have hGm : ∀ j, MeasurableSet (G j) := by
      intro j
      have : G j = ⋃ i, {v : Fin n → ℝ | α j < Fmax μ (v i)} := by ext v; simp [G]
      rw [this]
      exact MeasurableSet.iUnion fun i =>
        measurableSet_lt measurable_const (hmeasF.comp (measurable_pi_apply _))
    have hPG : ∀ j, ((Measure.pi μ) (G j)).toReal = 1 - α j := by
      intro j
      have hc : (G j)ᶜ = {v | ∀ i, v ((1 : Equiv.Perm (Fin n)) i) ∈ S j} := by
        ext v; simp [G, S]
      have hGc : G j = ({v | ∀ i, v ((1 : Equiv.Perm (Fin n)) i) ∈ S j})ᶜ := by
        rw [← hc, compl_compl]
      have hbm : MeasurableSet {v : Fin n → ℝ | ∀ i, v ((1 : Equiv.Perm (Fin n)) i) ∈ S j} := by
        rw [← hc]; exact (hGm j).compl
      rw [hGc, prob_compl_eq_one_sub hbm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        box_prob']
      simp only [ENNReal.toReal_one, Equiv.Perm.coe_one, id]
      rw [← hcol j]
    -- pointwise counting
    set cR : ℝ := (n.factorial : ℝ) / n with hcR
    have hpt : ∀ v : Fin n → ℝ,
        cR * ∑ j ∈ Pk, (G j).indicator (1 : (Fin n → ℝ) → ℝ) v ≤
          ∑ σ : Equiv.Perm (Fin n), (E σ).indicator (1 : (Fin n → ℝ) → ℝ) v := by
      intro v
      obtain ⟨istar, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => Fmax μ (v i))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have h1 : cR * ∑ j ∈ Pk, (G j).indicator (1 : (Fin n → ℝ) → ℝ) v =
          ∑ σ : Equiv.Perm (Fin n), ∑ j ∈ Pk,
            (if σ j = istar then (G j).indicator (1 : (Fin n → ℝ) → ℝ) v else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          hfib j istar, mul_comm]
      rw [h1]
      apply Finset.sum_le_sum
      intro σ _
      have h2 : ∀ j, (if σ j = istar then (G j).indicator (1 : (Fin n → ℝ) → ℝ) v else 0) =
          if σ.symm istar = j then (G j).indicator (1 : (Fin n → ℝ) → ℝ) v else 0 := by
        intro j
        congr 1
        apply propext
        rw [Equiv.symm_apply_eq]
        exact eq_comm
      simp_rw [h2]
      rw [Finset.sum_ite_eq]
      split_ifs with hj0
      · by_cases hvG : v ∈ G (σ.symm istar)
        · have hvE : v ∈ E σ := by
            obtain ⟨i, hi⟩ := hvG
            refine ⟨σ.symm istar, by simpa [hPk] using hj0, ?_⟩
            show α (σ.symm istar) < Fmax μ (v (σ (σ.symm istar)))
            rw [Equiv.apply_symm_apply]
            exact lt_of_lt_of_le hi (hmax i (Finset.mem_univ _))
          rw [Set.indicator_of_mem hvG, Set.indicator_of_mem hvE]
        · rw [Set.indicator_of_notMem hvG]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    -- integrate
    have hint : ∀ (s : Set (Fin n → ℝ)), MeasurableSet s →
        Integrable (s.indicator (1 : (Fin n → ℝ) → ℝ)) (Measure.pi μ) := fun s hs =>
      (integrable_const (1 : ℝ)).indicator hs
    have hI := integral_mono (μ := Measure.pi μ)
      ((integrable_finsetSum _ fun j _ => hint _ (hGm j)).const_mul cR)
      (integrable_finsetSum _ fun σ _ => hint _ (hEm σ)) hpt
    rw [integral_const_mul, integral_finsetSum _ fun j _ => hint _ (hGm j),
      integral_finsetSum _ fun σ _ => hint _ (hEm σ)] at hI
    simp only [integral_indicator_one (hGm _), integral_indicator_one (hEm _),
      measureReal_def] at hI
    simp_rw [hPG, hPE] at hI
    rw [hprob]
    have : 1 / (n : ℝ) * ∑ j ∈ Pk, (1 - α j) = 1 / (n.factorial : ℝ) * (cR * ∑ j ∈ Pk, (1 - α j)) := by
      rw [hcR]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hI (by positivity)
  · ------------------------------------------------------------------ upper bound (AM-GM)
    rw [hprob]
    have hw : ∑ _σ : Equiv.Perm (Fin n), (1 / (n.factorial : ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hAMGM := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (fun _ : Equiv.Perm (Fin n) => 1 / (n.factorial : ℝ)) Y (fun _ _ => by positivity) hw
      (fun σ _ => hY0 σ)
    -- the geometric mean equals `(∏_{j<k} α_j)^{1/n}`
    have hgeo : ∏ σ : Equiv.Perm (Fin n), Y σ ^ (1 / (n.factorial : ℝ)) =
        (∏ j ∈ Pk, α j) ^ ((1 : ℝ) / n) := by
      have step1 : ∀ σ : Equiv.Perm (Fin n), Y σ ^ (1 / (n.factorial : ℝ)) =
          ∏ j ∈ Pk, x (σ j) j ^ (1 / (n.factorial : ℝ)) := by
        intro σ
        rw [Real.finsetProd_rpow _ _ (fun j _ => hx0 _ _)]
      simp_rw [step1]
      rw [Finset.prod_comm]
      rw [← Real.finsetProd_rpow _ _ (fun j _ => (hα j).1)]
      apply Finset.prod_congr rfl
      intro j _
      rw [← hcol j, ← Real.finsetProd_rpow _ _ (fun i _ => hx0 _ _)]
      rw [← Finset.prod_fiberwise_of_maps_to' (g := fun σ : Equiv.Perm (Fin n) => σ j)
        (t := Finset.univ) (fun σ _ => Finset.mem_univ _)
        (fun i => x i j ^ (1 / (n.factorial : ℝ)))]
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (hx0 _ _), hfib j i]
      congr 1
      field_simp
    rw [hgeo] at hAMGM
    have hsum : ∑ σ : Equiv.Perm (Fin n), 1 / (n.factorial : ℝ) * Y σ =
        1 / (n.factorial : ℝ) * ∑ σ : Equiv.Perm (Fin n), Y σ := by
      rw [Finset.mul_sum]
    rw [hsum] at hAMGM
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, mul_sub, mul_one]
    have : 1 / (n.factorial : ℝ) * (n.factorial : ℝ) = 1 := by field_simp
    rw [this]
    linarith

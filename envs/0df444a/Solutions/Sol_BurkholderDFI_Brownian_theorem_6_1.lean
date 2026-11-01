-- Prove2me | solution 1 for BurkholderDFI.Brownian.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T11:11:45.766591+00:00
-- url     : https://prove2.me/submissions/d2a97a1c-3a3b-487d-89b6-446300e7213d

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Definitions.Def_BurkholderDFI_Brownian_Process
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section

end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma natField_le {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable (X t)) (s : ℝ≥0) :
    natField X s ≤ mΩ := by
  exact iSup_le fun t => iSup_le fun _ => (hX t).comap_le

omit [MeasurableSpace Ω] in
lemma natField_mono (X : ℝ≥0 → Ω → ℝ) : Monotone (natField X) := by
  intro s t hst
  exact iSup_le fun u => iSup_le fun hu =>
    le_iSup_of_le u (le_iSup_of_le (hu.trans hst) le_rfl)

omit [MeasurableSpace Ω] in
lemma measurable_eval_natField (X : ℝ≥0 → Ω → ℝ) {s t : ℝ≥0} (ht : t ≤ s) :
    @Measurable Ω ℝ (natField X s) inferInstance (X t) := by
  exact measurable_iff_comap_le.mpr
    (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

omit [MeasurableSpace Ω] in
lemma natField_eq_past (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    natField X s = MeasurableSpace.comap (fun ω (t : Set.Iic s) => X t ω) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · exact iSup_le fun t => iSup_le fun ht => le_iSup_of_le ⟨t, ht⟩ le_rfl
  · exact iSup_le fun t => le_iSup_of_le t.1 (le_iSup_of_le t.2 le_rfl)

lemma indep_future_past {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    (s : ℝ≥0) {E : Type*} [MeasurableSpace E] {Y : Ω → E}
    (hY : @Measurable Ω E (natField X s) inferInstance Y) :
    IndepFun (fun ω t => X (s+t) ω-X s ω) Y P := by
  rw [IndepFun_iff]
  intro A B hA hB
  apply (hX.1.toIsPreBrownianReal.indepFun_shift s).meas_inter hA
  rw [← natField_eq_past]
  exact hY.comap_le _ hB

lemma indep_increment_past {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    (s t : ℝ≥0) {E : Type*} [MeasurableSpace E] {Y : Ω → E}
    (hY : @Measurable Ω E (natField X s) inferInstance Y) :
    IndepFun (fun ω => X (s+t) ω-X s ω) Y P := by
  simpa only [Function.comp_def, id_eq] using
    (indep_future_past hX s hY).comp (measurable_pi_apply t) measurable_id

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BurkholderDFI.Brownian.Fresh

lemma bm_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P) (s : ℝ≥0) :
    IsBM (fun t ω => X (s+t) ω-X s ω) P := by
  refine ⟨hX.1.shift s, ?_, ?_⟩
  · intro t
    exact (hX.2.1 _).sub (hX.2.1 _)
  · intro ω
    exact ((hX.2.2 ω).comp (continuous_const.add continuous_id)).sub continuous_const

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

lemma gaussian_pdf_le_inv {v : ℝ≥0} {lam : ℝ} (hl : 0 < lam)
    (hv : lam ^ 2 ≤ 2 * Real.pi * v) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ lam⁻¹ := by
  have hs : lam ≤ Real.sqrt (2 * Real.pi * v) := by
    exact (Real.le_sqrt (le_of_lt hl) (by positivity)).mpr hv
  have he : Real.exp (-(x-0)^2 / (2*(v:ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
      unfold gaussianPDFReal
      exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)
    _ ≤ lam⁻¹ := inv_anti₀ hl hs

lemma gaussian_small_ball {v : ℝ≥0} {lam δ : ℝ} (hl : 0 < lam) (hd : 0 ≤ δ)
    (hv : v ≠ 0) (hvar : lam^2 ≤ 2 * Real.pi * v) :
    gaussianReal 0 v {x | |x| ≤ 2*δ*lam} ≤ ENNReal.ofReal (4*δ) := by
  have hb : 0 ≤ 2*δ*lam := by positivity
  have he : {x : ℝ | |x| ≤ 2*δ*lam} = Icc (-(2*δ*lam)) (2*δ*lam) := by
    ext x
    change |x| ≤ 2*δ*lam ↔ -(2*δ*lam) ≤ x ∧ x ≤ 2*δ*lam
    exact abs_le
  rw [he, gaussianReal_apply 0 hv]
  calc
    (∫⁻ x in Icc (-(2*δ*lam)) (2*δ*lam), gaussianPDF 0 v x)
        ≤ ∫⁻ _x in Icc (-(2*δ*lam)) (2*δ*lam), ENNReal.ofReal lam⁻¹ := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussian_pdf_le_inv hl hvar x)
    _ = ENNReal.ofReal (4*δ) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma increment_small_ball {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    (s u : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[natField X s] A)
    {lam δ : ℝ} (hl : 0 < lam) (hd : 0 ≤ δ) (hu : u ≠ 0)
    (hvar : lam^2 ≤ 2*Real.pi*u) :
    P (A ∩ {ω | |X (s+u) ω-X s ω| ≤ 2*δ*lam}) ≤ ENNReal.ofReal (4*δ) * P A := by
  have hi := @indep_increment_past Ω mΩ P X hX s u Ω (natField X s) id measurable_id
  have hb : MeasurableSet {x : ℝ | |x| ≤ 2*δ*lam} := isClosed_le continuous_abs continuous_const |>.measurableSet
  have he := hi.measure_inter_preimage_eq_mul _ _ hb hA
  have hlaw := ((bm_shift hX s).1.toIsPreBrownianReal.hasLaw_eval u).measure_eq hb
  change P ({ω | |X (s+u) ω-X s ω| ≤ 2*δ*lam} ∩ A) =
    P {ω | |X (s+u) ω-X s ω| ≤ 2*δ*lam} * P A at he
  rw [inter_comm, he, hlaw]
  exact mul_le_mul' (gaussian_small_ball hl hd hu hvar) le_rfl

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma stopping_ge_measurable {X : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTimeOf X τ) {s : ℝ≥0} (hs : 0 < s) :
    MeasurableSet[natField X s] {ω | (s : ℝ≥0∞) ≤ τ ω} := by
  simpa only [compl_ofPred, not_lt] using (hτ s hs).compl

lemma stopping_measurable {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable (X t))
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTimeOf X τ) : Measurable τ := by
  apply measurable_of_Iio
  intro a
  by_cases ha : a = ∞
  · subst a
    have he : τ ⁻¹' Iio ∞ = ⋃ n : ℕ, {ω | τ ω < ((n+1 : ℕ) : ℝ≥0∞)} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
        exact ⟨n, hn.trans_le (by exact_mod_cast Nat.le_succ n)⟩
      · rintro ⟨n, hn⟩
        exact hn.trans (ENNReal.natCast_lt_top _)
    rw [he]
    apply MeasurableSet.iUnion
    intro n
    simpa only [Nat.cast_add, Nat.cast_one, ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_natCast] using
      (natField_le hX _) _ (hτ (n+1) (by positivity))
  · lift a to ℝ≥0 using ha with a
    by_cases hz : a = 0
    · subst a
      simp
    · exact (natField_le hX _) _ (hτ a (pos_iff_ne_zero.mpr hz))

lemma measurable_random_eval {X : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => X t ω) (hm : ∀ t, Measurable (X t))
    {s : Ω → ℝ≥0} (hs : Measurable s) : Measurable (fun ω => X (s ω) ω) := by
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp (hs.prodMk measurable_id)

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

lemma continuous_stopped_time (b : ℝ≥0∞) :
    Continuous (fun t : ℝ≥0 => (min b (t : ℝ≥0∞)).toNNReal) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ENNReal.tendsto_toNNReal (ne_of_lt (lt_of_le_of_lt (min_le_right _ _)
    (ENNReal.coe_lt_top)))).comp
    ((continuous_const.min ENNReal.continuous_coe).tendsto t)

lemma measurable_maxStopped {X : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => X t ω) (hm : ∀ t, Measurable (X t))
    {τ : Ω → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable (fun ω => maxStopped X (τ ω) ω) := by
  have h : Measurable (⨆ t : ℝ≥0,
      fun ω => ENNReal.ofReal |X (min (τ ω) (t : ℝ≥0∞)).toNNReal ω|) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro t
      exact ENNReal.measurable_ofReal.comp
        (measurable_random_eval hc hm (ENNReal.measurable_toNNReal.comp
          (hτ.min measurable_const))).abs
    · intro ω
      exact (ENNReal.continuous_ofReal.comp
        (((hc ω).comp (continuous_stopped_time (τ ω))).abs)).lowerSemicontinuous
  have he : (⨆ t : ℝ≥0, fun ω => ENNReal.ofReal |X (min (τ ω) (t : ℝ≥0∞)).toNNReal ω|) =
      (fun ω => maxStopped X (τ ω) ω) := by
    funext ω
    exact iSup_apply
  rw [he] at h
  exact h

omit [MeasurableSpace Ω] in
lemma eval_le_maxStopped (X : ℝ≥0 → Ω → ℝ) (b : ℝ≥0∞) (ω : Ω)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ b) :
    ENNReal.ofReal |X t ω| ≤ maxStopped X b ω := by
  have h := le_iSup (fun s : ℝ≥0 => ENNReal.ofReal |X (min b (s : ℝ≥0∞)).toNNReal ω|) t
  simpa only [min_eq_right ht, ENNReal.toNNReal_coe] using! h

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*}

lemma maxStopped_gt_iff (X : ℝ≥0 → Ω → ℝ) (b : ℝ≥0∞) (ω : Ω)
    {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a < maxStopped X b ω ↔
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ b ∧ a < |X t ω| := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := lt_iSup_iff.mp h
    exact ⟨(min b (t : ℝ≥0∞)).toNNReal,
      ENNReal.coe_toNNReal_le_self.trans (min_le_left _ _),
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp ht⟩
  · rintro ⟨t, ht, hlt⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr hlt).trans_le
      (eval_le_maxStopped X b ω t ht)

lemma abs_eval_le_of_maxStopped_le (X : ℝ≥0 → Ω → ℝ) (b : ℝ≥0∞) (ω : Ω)
    {a : ℝ} (ha : 0 ≤ a) (h : maxStopped X b ω ≤ ENNReal.ofReal a)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ b) : |X t ω| ≤ a := by
  exact (ENNReal.ofReal_le_ofReal_iff ha).mp ((eval_le_maxStopped X b ω t ht).trans h)

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open scoped ENNReal NNReal

lemma half_rpow_sq (x : ℝ≥0∞) : (x ^ (1/2 : ℝ)) ^ (2 : ℕ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma lt_half_rpow_iff (a x : ℝ≥0∞) : a < x^(1/2 : ℝ) ↔ a^2 < x := by
  have h := ENNReal.rpow_lt_rpow_iff (x := a) (y := x^(1/2 : ℝ)) (by norm_num : (0:ℝ)<2)
  simpa only [ENNReal.rpow_two, half_rpow_sq] using h.symm

lemma half_rpow_le_iff (a x : ℝ≥0∞) : x^(1/2 : ℝ) ≤ a ↔ x ≤ a^2 := by
  have h := ENNReal.rpow_le_rpow_iff (x := x^(1/2 : ℝ)) (y := a) (by norm_num : (0:ℝ)<2)
  simpa only [ENNReal.rpow_two, half_rpow_sq] using h.symm

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma lower_good_lambda_nnreal {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTimeOf X τ)
    (lam δ : ℝ≥0) (hl : 0 < lam) :
    P {ω | 2*(lam : ℝ≥0∞) < (τ ω)^(1/2 : ℝ) ∧
      maxStopped X (τ ω) ω ≤ (δ : ℝ≥0∞)*lam} ≤
      (4*(δ : ℝ≥0∞))*P {ω | (lam : ℝ≥0∞) < (τ ω)^(1/2 : ℝ)} := by
  let s : ℝ≥0 := 2*lam^2
  have hs : 0 < s := by dsimp [s]; positivity
  have hst : ((s+s : ℝ≥0) : ℝ≥0∞) = (2*(lam : ℝ≥0∞))^2 := by
    simp only [s, ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
    ring
  let A : Set Ω := {ω | (s : ℝ≥0∞) ≤ τ ω}
  have hA : MeasurableSet[natField X s] A := stopping_ge_measurable hτ hs
  have hsub : {ω | 2*(lam : ℝ≥0∞) < (τ ω)^(1/2 : ℝ) ∧
      maxStopped X (τ ω) ω ≤ (δ : ℝ≥0∞)*lam} ⊆
      A ∩ {ω | |X (s+s) ω-X s ω| ≤ 2*(δ:ℝ)*lam} := by
    intro ω hω
    have ht : ((s+s : ℝ≥0) : ℝ≥0∞) < τ ω := by
      rw [hst]
      exact (lt_half_rpow_iff _ _).mp hω.1
    have hle : (s : ℝ≥0∞) ≤ τ ω :=
      (show (s : ℝ≥0∞) ≤ ((s+s : ℝ≥0) : ℝ≥0∞) by exact_mod_cast (le_add_of_nonneg_right (show 0 ≤ s from zero_le))).trans ht.le
    have hm : maxStopped X (τ ω) ω ≤ ENNReal.ofReal ((δ:ℝ)*lam) := by
      simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg δ), ENNReal.ofReal_coe_nnreal] using hω.2
    have h1 := abs_eval_le_of_maxStopped_le X (τ ω) ω (by positivity) hm s hle
    have h2 := abs_eval_le_of_maxStopped_le X (τ ω) ω (by positivity) hm (s+s) ht.le
    refine ⟨hle, ?_⟩
    change |X (s+s) ω-X s ω| ≤ 2*(δ:ℝ)*lam
    calc
      _ ≤ |X (s+s) ω| + |X s ω| := abs_sub _ _
      _ ≤ 2*(δ:ℝ)*lam := by linarith
  have hvar : (lam:ℝ)^2 ≤ 2*Real.pi*s := by
    have hp := Real.pi_gt_three
    simp only [s, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow]
    nlinarith [sq_nonneg (lam:ℝ)]
  have hbound := increment_small_ball hX s s hA (show 0 < (lam:ℝ) from hl)
    (NNReal.coe_nonneg δ) hs.ne' hvar
  have hA' : A ⊆ {ω | (lam : ℝ≥0∞) < (τ ω)^(1/2 : ℝ)} := by
    intro ω hω
    apply (lt_half_rpow_iff _ _).mpr
    have hh : lam^2 < s := by dsimp [s]; nlinarith [sq_pos_of_pos hl]
    exact (show (lam : ℝ≥0∞)^2 < (s : ℝ≥0∞) by exact_mod_cast hh).trans_le hω
  calc
    _ ≤ P (A ∩ {ω | |X (s+s) ω-X s ω| ≤ 2*(δ:ℝ)*lam}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (4*(δ:ℝ))*P A := hbound
    _ ≤ (4*(δ : ℝ≥0∞))*P {ω | (lam : ℝ≥0∞) < (τ ω)^(1/2 : ℝ)} := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
      norm_num only [ENNReal.ofReal_ofNat]
      exact mul_le_mul' le_rfl (measure_mono hA')

end BurkholderDFI.Brownian.Fresh
end

section

open Filter Topology
open scoped NNReal

namespace BurkholderDFI.Brownian.Fresh

noncomputable def gridTime (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) * T / (n+1)

lemma gridTime_zero (T : ℝ≥0) (n : ℕ) : gridTime T n 0 = 0 := by
  simp [gridTime]

lemma gridTime_last (T : ℝ≥0) (n : ℕ) : gridTime T n (n+1) = T := by
  simp [gridTime, Nat.cast_add, Nat.cast_one]

lemma gridTime_mono (T : ℝ≥0) (n : ℕ) : Monotone (gridTime T n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) T.2)
    (by positivity)

lemma gridTime_le (T : ℝ≥0) (n i : ℕ) (hi : i ≤ n+1) : gridTime T n i ≤ T := by
  simpa only [gridTime_last] using gridTime_mono T n hi

lemma gridTime_adjacent (T : ℝ≥0) (n i : ℕ) :
    (gridTime T n (i+1) : ℝ) - gridTime T n i = (T : ℝ) / (n+1) := by
  simp only [gridTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  ring

lemma gridTime_approx {T x : ℝ≥0} (hT : 0 < T) (hx : x ≤ T) (n : ℕ) :
    ∃ i ≤ n+1, gridTime T n i ≤ x ∧
      (x : ℝ) - gridTime T n i < (T : ℝ)/(n+1) := by
  let h : ℝ := (T : ℝ)/(n+1)
  have hn : (0 : ℝ) < n+1 := by positivity
  have hh : 0 < h := div_pos (by exact_mod_cast hT) hn
  let i : ℕ := ⌊(x : ℝ)/h⌋₊
  have hlow : (i : ℝ)*h ≤ x :=
    (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg x.2 hh.le))
  have hupp : (x : ℝ) < ((i : ℝ)+1)*h :=
    (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one ((x : ℝ)/h))
  have hmul : ((n : ℝ)+1)*h = T := by dsimp [h]; field_simp
  have hi : i ≤ n+1 := by
    have hx' : (x : ℝ) ≤ T := by exact_mod_cast hx
    have : (i : ℝ) ≤ (n : ℝ)+1 := by nlinarith
    exact_mod_cast this
  have hgrid : (gridTime T n i : ℝ) = (i : ℝ)*h := by
    simp only [gridTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, h]
    ring
  refine ⟨i, hi, ?_, ?_⟩
  · exact_mod_cast (show (gridTime T n i : ℝ) ≤ x by rw [hgrid]; exact hlow)
  · rw [hgrid]
    change (x : ℝ) - (i : ℝ)*h < h
    nlinarith

lemma grid_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ => (T : ℝ)/(n+1)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)

end BurkholderDFI.Brownian.Fresh
end

section

open Filter Topology
open scoped NNReal

namespace BurkholderDFI.Brownian.Fresh

lemma grid_detect {T t : ℝ≥0} (hT : 0 < T) (ht : t ≤ T)
    {f : ℝ≥0 → ℝ} (hf : Continuous f) {a : ℝ} (ha : a < |f t|) :
    ∀ᶠ n : ℕ in atTop, ∃ i ≤ n+1, gridTime T n i ≤ t ∧ a < |f (gridTime T n i)| := by
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (x := t))
    (|f t|-a) (sub_pos.mpr ha)
  have hn := (grid_mesh_tendsto T).eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn
  obtain ⟨i, hi, hit, hei⟩ := gridTime_approx hT ht n
  have hdist : dist (gridTime T n i) t < δ := by
    change dist (gridTime T n i : ℝ) (t : ℝ) < δ
    rw [Real.dist_eq, abs_of_nonpos (by exact sub_nonpos.mpr (show (gridTime T n i : ℝ) ≤ t from hit))]
    linarith
  have hh := hd hdist
  rw [Real.dist_eq] at hh
  have hab := abs_add_le (f t - f (gridTime T n i)) (f (gridTime T n i))
  rw [sub_add_cancel, abs_sub_comm] at hab
  exact ⟨i, hi, hit, by linarith⟩

lemma grid_increments_small {T : ℝ≥0} {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ≤ n,
      |f (gridTime T n (i+1)) - f (gridTime T n i)| < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (hf.continuousOn : ContinuousOn f (Set.Icc 0 T))
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  have hn := (grid_mesh_tendsto T).eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn i hi
  have hdist : dist (gridTime T n (i+1)) (gridTime T n i) < δ := by
    change dist (gridTime T n (i+1) : ℝ) (gridTime T n i : ℝ) < δ
    rw [Real.dist_eq, abs_of_nonneg (by exact sub_nonneg.mpr (show (gridTime T n i : ℝ) ≤ gridTime T n (i+1) from
      gridTime_mono T n (Nat.le_succ i))), gridTime_adjacent]
    exact hn
  simpa only [Real.dist_eq] using hd (gridTime T n (i+1))
    ⟨by positivity, gridTime_le T n (i+1) (by omega)⟩
    (gridTime T n i) ⟨by positivity, gridTime_le T n i (by omega)⟩ hdist

end BurkholderDFI.Brownian.Fresh
end

section

open Filter
open scoped NNReal

namespace BurkholderDFI.Brownian.Fresh

lemma first_crossing_small {y : ℕ → ℝ} {a : ℝ} (ha : 0 < a) (hzero : y 0 = 0)
    {j : ℕ} (hj : a < |y j|)
    (hinc : ∀ i < j, |y (i+1)-y i| < a/2) :
    ∃ i ≤ j, 0 < i ∧ a < |y i| ∧ |y i| ≤ 3*a/2 ∧ ∀ l < i, |y l| ≤ a := by
  classical
  have hex : ∃ i, a < |y i| := ⟨j, hj⟩
  let i := Nat.find hex
  have hi : i ≤ j := Nat.find_min' hex hj
  have hai : a < |y i| := Nat.find_spec hex
  have hprev : ∀ l < i, |y l| ≤ a := by
    intro l hl
    exact le_of_not_gt (Nat.find_min hex hl)
  have hip : 0 < i := by
    by_contra h
    have hiz : i = 0 := by omega
    rw [hiz, hzero, abs_zero] at hai
    linarith
  have hp := hprev (i-1) (by omega)
  have hd := hinc (i-1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at hd
  have hab := abs_add_le (y i-y (i-1)) (y (i-1))
  rw [sub_add_cancel] at hab
  exact ⟨i, hi, hip, hai, by linarith, hprev⟩

lemma grid_first_crossing {T t : ℝ≥0} (hT : 0 < T) (ht : t ≤ T)
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hzero : f 0 = 0)
    {a : ℝ} (ha : 0 < a) (hat : 2*a < |f t|) :
    ∀ᶠ n : ℕ in atTop, ∃ i ≤ n+1,
      gridTime T n i ≤ t ∧ a < |f (gridTime T n i)| ∧
      |f (gridTime T n i)| ≤ 3*a/2 ∧
      (∀ j < i, |f (gridTime T n j)| ≤ a) ∧
      ∃ u ≤ T, a/2 < |f (gridTime T n i+u)-f (gridTime T n i)| := by
  filter_upwards [grid_detect hT ht hf hat, grid_increments_small hf (by linarith : 0 < a/2)]
    with n hn hinc
  obtain ⟨j, hj, hjt, haj⟩ := hn
  obtain ⟨i, hij, _, hai, hbound, hprev⟩ := first_crossing_small (y := fun l => f (gridTime T n l)) (j := j) ha
    (by simpa only [gridTime_zero] using hzero : f (gridTime T n 0) = 0)
    (by linarith : a < |f (gridTime T n j)|)
    (fun l hl => hinc l (by omega))
  have hit : gridTime T n i ≤ t := (gridTime_mono T n hij).trans hjt
  refine ⟨i, hij.trans hj, hit, hai, hbound, hprev, t-gridTime T n i,
    (tsub_le_self : t-gridTime T n i ≤ t).trans ht, ?_⟩
  rw [add_tsub_cancel_of_le hit]
  have hab := abs_add_le (f t-f (gridTime T n i)) (f (gridTime T n i))
  rw [sub_add_cancel] at hab
  linarith

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal

namespace BurkholderDFI.Brownian.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
  {τ : Ω → ℝ≥0∞}

noncomputable def crossingEvent (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞)
    (T : ℝ≥0) (n i : ℕ) (a : ℝ) : Set Ω :=
  {ω | (gridTime T n i : ℝ≥0∞) ≤ τ ω ∧ a < |X (gridTime T n i) ω| ∧
    |X (gridTime T n i) ω| ≤ 3*a/2 ∧ ∀ j < i, |X (gridTime T n j) ω| ≤ a}

omit [MeasurableSpace Ω] in
lemma crossingEvent_measurable (hτ : IsStoppingTimeOf X τ) (T : ℝ≥0)
    (n i : ℕ) (a : ℝ) :
    MeasurableSet[natField X (gridTime T n i)] (crossingEvent X τ T n i a) := by
  let : MeasurableSpace Ω := natField X (gridTime T n i)
  have hs : MeasurableSet[natField X (gridTime T n i)]
      {ω | (gridTime T n i : ℝ≥0∞) ≤ τ ω} := by
    by_cases hz : gridTime T n i = 0
    · simp [hz]
    · exact stopping_ge_measurable hτ (pos_iff_ne_zero.mpr hz)
  have hi := (measurable_eval_natField X (s := gridTime T n i) le_rfl).abs
  have hp : MeasurableSet[natField X (gridTime T n i)]
      {ω | ∀ j < i, |X (gridTime T n j) ω| ≤ a} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact measurableSet_le
      (measurable_eval_natField X (gridTime_mono T n hj.le)).abs measurable_const
  exact hs.inter ((measurableSet_lt measurable_const hi).inter
    ((measurableSet_le hi measurable_const).inter hp))

omit [MeasurableSpace Ω] in
lemma crossingEvent_disjoint (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞)
    (T : ℝ≥0) (n : ℕ) (a : ℝ) :
    Pairwise (Disjoint on (fun i : Fin (n+2) => crossingEvent X τ T n i a)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro ω hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj.2.2.2 i h)) hi.2.1
  · exact (not_lt_of_ge (hi.2.2.2 j h)) hj.2.1

omit [MeasurableSpace Ω] in
lemma crossingEvent_subset (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞)
    (T : ℝ≥0) (n i : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    crossingEvent X τ T n i a ⊆ {ω | ENNReal.ofReal a < maxStopped X (τ ω) ω} := by
  intro ω hω
  exact (maxStopped_gt_iff X (τ ω) ω ha).2 ⟨gridTime T n i, hω.1, hω.2.1⟩

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma bm_memLp_two (hX : IsBM X P) (t : ℝ≥0) : MemLp (X t) 2 P :=
  (hX.1.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

omit [IsProbabilityMeasure P] in
lemma bm_integrable_sq (hX : IsBM X P) (t : ℝ≥0) :
    Integrable (fun ω => (X t ω) ^ 2) P :=
  (bm_memLp_two hX t).integrable_sq

lemma bm_integral_sq (hX : IsBM X P) (t : ℝ≥0) :
    (∫ ω, (X t ω) ^ 2 ∂P) = t := by
  have hh := hX.1.toIsPreBrownianReal.covariance_eval t t
  rw [covariance_eq_sub (bm_memLp_two hX t) (bm_memLp_two hX t),
    hX.1.toIsPreBrownianReal.integral_eval, zero_mul, sub_zero, min_self] at hh
  simpa only [pow_two, Pi.mul_apply] using! hh

omit [IsProbabilityMeasure P] in
lemma bm_increment_cross_zero (hX : IsBM X P) (s t : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[natField X s] A) :
    (∫ ω in A, (X (s+t) ω-X s ω)*X s ω ∂P) = 0 := by
  have hAm : MeasurableSet A := natField_le hX.2.1 s A hA
  have hi := indep_increment_past hX s t
    ((measurable_eval_natField X le_rfl).indicator hA)
  have hm : Measurable (fun ω => X (s+t) ω-X s ω) :=
    (hX.2.1 _).sub (hX.2.1 _)
  have he := hi.integral_fun_mul_eq_mul_integral hm.aestronglyMeasurable
    ((hX.2.1 s).indicator hAm).aestronglyMeasurable
  have hz : (∫ ω, X (s+t) ω-X s ω ∂P) = 0 := by
    rw [integral_sub (hX.1.toIsPreBrownianReal.integrable_eval _)
      (hX.1.toIsPreBrownianReal.integrable_eval _),
      hX.1.toIsPreBrownianReal.integral_eval,
      hX.1.toIsPreBrownianReal.integral_eval, sub_self]
  rw [hz, zero_mul] at he
  rw [← integral_indicator hAm]
  convert he using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases h : ω ∈ A <;> simp [h]

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian.Fresh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℕ ‹MeasurableSpace Ω›} {Y : ℕ → Ω → ℝ}

theorem discrete_square_max_bound
    (hsub : Submartingale (fun k ω => (Y k ω) ^ 2) F P)
    (n : ℕ) (a T : ℝ) (ha : 0 ≤ a)
    (hT : (∫ ω, (Y n ω) ^ 2 ∂P) ≤ T) :
    ENNReal.ofReal (a ^ 2) * P {ω | ∃ k ≤ n, a < |Y k ω|} ≤ ENNReal.ofReal T := by
  classical
  let e : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩
  have hm := maximal_ineq hsub (fun k ω => sq_nonneg (Y k ω)) (ε := e) n
  have hs : {ω | ∃ k ≤ n, a < |Y k ω|} ⊆
      {ω | (e : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => (Y k ω) ^ 2)} := by
    rintro ω ⟨k, hk, hka⟩
    have hsq : a ^ 2 ≤ (Y k ω) ^ 2 := by
      nlinarith [sq_abs (Y k ω)]
    exact hsq.trans (Finset.le_sup' (fun k => (Y k ω) ^ 2)
      (Finset.mem_range.mpr (by omega)))
  have hi : (∫ ω in {ω | (e : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => (Y k ω) ^ 2)}, (Y n ω) ^ 2 ∂P) ≤ T :=
    (setIntegral_le_integral (hsub.integrable n)
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y n ω)))).trans hT
  have he : (e : ℝ≥0∞) = ENNReal.ofReal (a ^ 2) := by
    exact (ENNReal.ofReal_coe_nnreal).symm
  rw [he] at hm
  exact (mul_le_mul' le_rfl (measure_mono hs)).trans (hm.trans (ENNReal.ofReal_le_ofReal hi))

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian.Fresh
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma bm_square_setIntegral_le (hX : IsBM X P) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[natField X s] A) :
    (∫ ω in A, (X s ω)^2 ∂P) ≤ ∫ ω in A, (X t ω)^2 ∂P := by
  have hz := bm_increment_cross_zero hX s (t-s) hA
  rw [add_tsub_cancel_of_le hst] at hz
  have hmul : Integrable (fun ω => (X t ω-X s ω)*X s ω) P :=
    ((bm_memLp_two hX t).sub (bm_memLp_two hX s)).integrable_mul (bm_memLp_two hX s)
  have hh : (∫ ω in A, (X s ω)^2 ∂P) ≤
      ∫ ω in A, (X t ω)^2 - 2*((X t ω-X s ω)*X s ω) ∂P := by
    apply integral_mono_ae (bm_integrable_sq hX s).integrableOn
      ((bm_integrable_sq hX t).sub (hmul.const_mul 2)).integrableOn
    exact Filter.Eventually.of_forall (fun ω => by
      change (X s ω)^2 ≤ (X t ω)^2 - 2*((X t ω-X s ω)*X s ω)
      nlinarith [sq_nonneg (X t ω-X s ω)])
  rw [integral_sub (bm_integrable_sq hX t).integrableOn (hmul.const_mul 2).integrableOn,
    integral_const_mul, hz, mul_zero, sub_zero] at hh
  exact hh

def sampleField (hX : IsBM X P) (times : ℕ → ℝ≥0) (ht : Monotone times) :
    Filtration ℕ mΩ where
  seq n := natField X (times n)
  mono' := (natField_mono X).comp ht
  le' n := natField_le hX.2.1 (times n)

lemma sampled_square_submartingale (hX : IsBM X P) (times : ℕ → ℝ≥0)
    (ht : Monotone times) :
    Submartingale (fun n ω => (X (times n) ω)^2) (sampleField hX times ht) P := by
  apply submartingale_of_setIntegral_le
  · intro n
    exact ((measurable_eval_natField X le_rfl).pow_const 2).stronglyMeasurable
  · intro n
    exact bm_integrable_sq hX _
  · intro i j hij A hA
    exact bm_square_setIntegral_le hX (ht hij) hA

lemma sampled_max_bound (hX : IsBM X P) (times : ℕ → ℝ≥0)
    (ht : Monotone times) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (a^2) * P {ω | ∃ k ≤ n, a < |X (times k) ω|} ≤
      (times n : ℝ≥0∞) := by
  have hh := discrete_square_max_bound (sampled_square_submartingale hX times ht)
    n a (times n) ha (bm_integral_sq hX (times n)).le
  simpa only [ENNReal.ofReal_coe_nnreal] using hh

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory Filter
open scoped ENNReal

namespace BurkholderDFI.Brownian.Fresh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measure_le_of_eventually_mem {A : Set Ω} {E : ℕ → Set Ω} {C : ℝ≥0∞}
    (hA : ∀ ω ∈ A, ∀ᶠ n in atTop, ω ∈ E n) (hE : ∀ n, P (E n) ≤ C) :
    P A ≤ C := by
  let F : ℕ → Set Ω := fun N => ⋂ n ≥ N, E n
  have hF : Monotone F := by
    intro N M hNM ω hω
    simp only [F, Set.mem_iInter] at hω ⊢
    intro n hn
    exact hω n (hNM.trans hn)
  have hsub : A ⊆ ⋃ N, F N := by
    intro ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hA ω hω)
    exact Set.mem_iUnion.2 ⟨N, by simpa only [F, Set.mem_iInter] using hN⟩
  refine (measure_mono hsub).trans ?_
  rw [hF.measure_iUnion]
  apply iSup_le
  intro N
  refine (measure_mono ?_).trans (hE N)
  intro ω hω
  exact Set.mem_iInter.1 (Set.mem_iInter.1 hω N) le_rfl

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

lemma sampled_max_div_bound (hX : IsBM X P) (times : ℕ → ℝ≥0)
    (ht : Monotone times) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ k ≤ n, a < |X (times k) ω|} ≤
      (times n : ℝ≥0∞) / ENNReal.ofReal (a^2) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ha))))
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa only [mul_comm] using sampled_max_bound hX times ht n a ha.le

lemma continuous_max_bound (hX : IsBM X P) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ t ≤ T, a < |X t ω|} ≤ (T : ℝ≥0∞) / ENNReal.ofReal (a^2) := by
  by_cases hT : T = 0
  · subst T
    have hh := sampled_max_div_bound hX (fun _ => 0) monotone_const 0 ha
    simpa only [Nat.le_zero, exists_eq_left, nonpos_iff_eq_zero] using hh
  · have hTpos : 0 < T := lt_of_le_of_ne (by positivity) (Ne.symm hT)
    apply measure_le_of_eventually_mem
      (E := fun n => {ω | ∃ i ≤ n+1, a < |X (gridTime T n i) ω|})
    · rintro ω ⟨t, ht, hat⟩
      filter_upwards [grid_detect hTpos ht (hX.2.2 ω) hat] with n hn
      obtain ⟨i, hi, _, hia⟩ := hn
      exact ⟨i, hi, hia⟩
    · intro n
      simpa only [gridTime_last] using
        sampled_max_div_bound hX (gridTime T n) (gridTime_mono T n) (n+1) ha

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace BurkholderDFI.Brownian.Fresh

noncomputable def pathGridEvent (T : ℝ≥0) (a : ℝ) : Set (ℝ≥0 → ℝ) :=
  ⋃ n : ℕ, ⋃ i : ℕ, ⋃ (_ : i ≤ n+1), {f | a < |f (gridTime T n i)|}

lemma measurableSet_pathGridEvent (T : ℝ≥0) (a : ℝ) : MeasurableSet (pathGridEvent T a) := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_lt measurable_const (measurable_pi_apply _).abs

lemma pathGridEvent_iff {T : ℝ≥0} {a : ℝ} {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    f ∈ pathGridEvent T a ↔ ∃ t ≤ T, a < |f t| := by
  simp only [pathGridEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, i, hi, hai⟩
    exact ⟨gridTime T n i, gridTime_le T n i hi, hai⟩
  · rintro ⟨t, ht, hat⟩
    by_cases hT : T = 0
    · subst T
      have ht0 : t = 0 := le_zero_iff.mp ht
      subst t
      exact ⟨0, 0, by omega, by simpa only [gridTime_zero] using hat⟩
    · obtain ⟨n, i, hi, _, hai⟩ := (grid_detect (lt_of_le_of_ne (by positivity) (Ne.symm hT))
        ht hf hat).exists
      exact ⟨n, i, hi, hai⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

lemma indep_future_natField (hX : IsBM X P) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω t => X (s+t) ω-X s ω) inferInstance)
      (natField X s) P := by
  rw [natField_eq_past]
  exact (IndepFun_iff_Indep _ _ _).1 (hX.1.toIsPreBrownianReal.indepFun_shift s)

lemma future_grid_indep (hX : IsBM X P) (s T : ℝ≥0) (a : ℝ)
    {E : Set Ω} (hE : MeasurableSet[natField X s] E) :
    IndepSet E ((fun ω t => X (s+t) ω-X s ω) ⁻¹' pathGridEvent T a) P := by
  apply (indep_future_natField hX s).symm.indepSet_of_measurableSet hE
  exact (measurableSet_pathGridEvent T a).preimage (comap_measurable _)

lemma future_grid_bound [IsProbabilityMeasure P] (hX : IsBM X P) (s T : ℝ≥0)
    {a : ℝ} (ha : 0 < a) :
    P ((fun ω t => X (s+t) ω-X s ω) ⁻¹' pathGridEvent T a) ≤
      (T : ℝ≥0∞) / ENNReal.ofReal (a^2) := by
  have he : ((fun ω t => X (s+t) ω-X s ω) ⁻¹' pathGridEvent T a) =
      {ω | ∃ t ≤ T, a < |X (s+t) ω-X s ω|} := by
    ext ω
    exact pathGridEvent_iff ((bm_shift hX s).2.2 ω)
  rw [he]
  exact continuous_max_bound (bm_shift hX s) T ha

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

namespace BurkholderDFI.Brownian.Fresh

lemma disjoint_trials_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {E F : ι → Set Ω} {B : Set Ω} {q : ℝ≥0∞}
    (hE : ∀ i, MeasurableSet (E i)) (hdis : Pairwise (Disjoint on E))
    (hsub : ∀ i, E i ⊆ B) (hind : ∀ i, IndepSet (E i) (F i) P)
    (hF : ∀ i, P (F i) ≤ q) :
    P (⋃ i, E i ∩ F i) ≤ q * P B := by
  classical
  calc
    P (⋃ i, E i ∩ F i) ≤ ∑' i, P (E i ∩ F i) := measure_iUnion_le _
    _ = ∑ i, P (E i ∩ F i) := tsum_fintype _
    _ ≤ ∑ i, q * P (E i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [(hind i).measure_inter_eq_mul, mul_comm]
      exact mul_le_mul' (hF i) le_rfl
    _ = q * ∑ i, P (E i) := (Finset.mul_sum _ _ _).symm
    _ = q * P (⋃ i, E i) := by rw [measure_iUnion hdis hE, tsum_fintype]
    _ ≤ q * P B := mul_le_mul' le_rfl (measure_mono (Set.iUnion_subset hsub))

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace BurkholderDFI.Brownian.Fresh
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}

lemma upper_good_lambda_time (hX : IsBM X P) (hτ : IsStoppingTimeOf X τ)
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ENNReal.ofReal (2*a) < maxStopped X (τ ω) ω ∧ τ ω ≤ (T : ℝ≥0∞)} ≤
      ((T : ℝ≥0∞) / ENNReal.ofReal ((a/2)^2)) *
        P {ω | ENNReal.ofReal a < maxStopped X (τ ω) ω} := by
  let A : Set Ω := {ω | ENNReal.ofReal (2*a) < maxStopped X (τ ω) ω ∧
    τ ω ≤ (T : ℝ≥0∞)}
  have he : P A = P (A ∩ {ω | X 0 ω = 0}) := by
    apply measure_congr
    filter_upwards [hX.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    change (ω ∈ A) = (ω ∈ A ∧ X 0 ω = 0)
    apply propext
    exact ⟨fun h => ⟨h, hω⟩, fun h => h.1⟩
  change P A ≤ _
  rw [he]
  by_cases hT : T = 0
  · have hempty : A ∩ {ω | X 0 ω = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro ω ⟨hω, hz⟩
      obtain ⟨t, ht, hat⟩ := (maxStopped_gt_iff X (τ ω) ω (by linarith : 0 ≤ 2*a)).1 hω.1
      have ht0 : t = 0 := by
        have : (t : ℝ≥0∞) ≤ 0 := by simpa only [hT, ENNReal.coe_zero] using ht.trans hω.2
        exact_mod_cast (le_zero_iff.mp this)
      rw [ht0, hz, abs_zero] at hat
      linarith
    rw [hempty, measure_empty]
    exact bot_le
  · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
    let E (n : ℕ) (i : Fin (n+2)) := crossingEvent X τ T n i a
    let F (n : ℕ) (i : Fin (n+2)) :=
      (fun ω t => X (gridTime T n i+t) ω-X (gridTime T n i) ω) ⁻¹'
        pathGridEvent T (a/2)
    apply measure_le_of_eventually_mem
      (E := fun n => ⋃ i : Fin (n+2), E n i ∩ F n i)
    · rintro ω ⟨hω, hz⟩
      obtain ⟨t, ht, hat⟩ := (maxStopped_gt_iff X (τ ω) ω (by linarith : 0 ≤ 2*a)).1 hω.1
      have htT : t ≤ T := by exact_mod_cast ht.trans hω.2
      filter_upwards [grid_first_crossing hTpos htT (hX.2.2 ω) hz ha hat] with n hn
      obtain ⟨i, hi, hit, hai, hib, hprev, u, hu, hau⟩ := hn
      apply Set.mem_iUnion.2
      refine ⟨⟨i, by omega⟩, ?_, ?_⟩
      · exact ⟨(show (gridTime T n i : ℝ≥0∞) ≤ t by exact_mod_cast hit).trans ht,
          hai, hib, hprev⟩
      · exact (pathGridEvent_iff ((bm_shift hX (gridTime T n i)).2.2 ω)).2 ⟨u, hu, hau⟩
    · intro n
      apply disjoint_trials_bound
        (E := E n) (F := F n)
        (q := (T : ℝ≥0∞) / ENNReal.ofReal ((a/2)^2))
      · intro i
        exact natField_le hX.2.1 _ _ (crossingEvent_measurable hτ T n i a)
      · exact crossingEvent_disjoint X τ T n a
      · intro i
        exact crossingEvent_subset X τ T n i ha.le
      · intro i
        exact future_grid_indep hX _ T (a/2) (crossingEvent_measurable hτ T n i a)
      · intro i
        exact future_grid_bound hX _ T (by linarith : 0 < a/2)

end BurkholderDFI.Brownian.Fresh
end

section

namespace BurkholderDFI.Brownian.Fresh
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma lower_good_lambda {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTimeOf X τ) (δ : ℝ≥0)
    {lam : ℝ} (hl : 0 < lam) :
    P {ω | 2*ENNReal.ofReal lam < (τ ω)^(1/2 : ℝ) ∧
      maxStopped X (τ ω) ω ≤ (δ : ℝ≥0∞)*ENNReal.ofReal lam} ≤
      (4*(δ : ℝ≥0∞))*P {ω | ENNReal.ofReal lam < (τ ω)^(1/2 : ℝ)} := by
  rw [ENNReal.ofReal_eq_coe_nnreal hl.le]
  exact lower_good_lambda_nnreal hX hτ ⟨lam, hl.le⟩ δ hl

lemma upper_good_lambda {X : ℝ≥0 → Ω → ℝ} (hX : IsBM X P)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTimeOf X τ) (δ : ℝ≥0) (hd : δ ≤ 1)
    {lam : ℝ} (hl : 0 < lam) :
    P {ω | 2*ENNReal.ofReal lam < maxStopped X (τ ω) ω ∧
      (τ ω)^(1/2 : ℝ) ≤ (δ : ℝ≥0∞)*ENNReal.ofReal lam} ≤
      (4*(δ : ℝ≥0∞))*P {ω | ENNReal.ofReal lam < maxStopped X (τ ω) ω} := by
  let T : ℝ≥0 := ⟨((δ:ℝ)*lam)^2, sq_nonneg _⟩
  have hTc : (T : ℝ≥0∞) = ENNReal.ofReal (((δ:ℝ)*lam)^2) :=
    (ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _)).symm
  have hT : (T : ℝ≥0∞) = ((δ : ℝ≥0∞)*ENNReal.ofReal lam)^2 := by
    rw [hTc]
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (NNReal.coe_nonneg δ),
      ENNReal.ofReal_coe_nnreal]
  have he : {ω | 2*ENNReal.ofReal lam < maxStopped X (τ ω) ω ∧
      (τ ω)^(1/2 : ℝ) ≤ (δ : ℝ≥0∞)*ENNReal.ofReal lam} =
      {ω | ENNReal.ofReal (2*lam) < maxStopped X (τ ω) ω ∧ τ ω ≤ (T : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, half_rpow_le_iff, hT,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_ofNat]
  rw [he]
  have hc : (T : ℝ≥0∞) / ENNReal.ofReal ((lam/2)^2) ≤ 4*(δ : ℝ≥0∞) := by
    rw [hTc]
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    have heq : ((δ:ℝ)*lam)^2 / (lam/2)^2 = 4*(δ:ℝ)^2 := by
      field_simp
      ring
    rw [heq]
    have hd' : (δ:ℝ) ≤ 1 := hd
    have hr : 4*(δ:ℝ)^2 ≤ 4*(δ:ℝ) := by nlinarith [δ.coe_nonneg]
    calc
      _ ≤ ENNReal.ofReal (4*(δ:ℝ)) := ENNReal.ofReal_le_ofReal hr
      _ = _ := by simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  exact (upper_good_lambda_time hX hτ T hl).trans (mul_le_mul' hc le_rfl)

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma phi_rightmost_level {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}
    (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c) (a : ℝ≥0∞)
    (ha : 0 < a) (hatop : a < Φ ∞) :
    ∃ x : ℝ≥0∞, 0 < x ∧ x ≠ ∞ ∧ Φ x = a ∧
      ∀ y : ℝ≥0∞, a < Φ y ↔ x < y := by
  have hne : {x : ℝ≥0∞ | Φ x = a}.Nonempty := by
    have hmem : a ∈ Set.Icc (Φ 0) (Φ ∞) := by
      rw [hΦ.zero]
      exact ⟨ha.le, hatop.le⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show (0 : ℝ≥0∞) ≤ ∞ from le_top)
      hΦ.cont.continuousOn hmem
    exact ⟨x, hx⟩
  have hcompact : IsCompact {x : ℝ≥0∞ | Φ x = a} :=
    (isClosed_eq hΦ.cont continuous_const).isCompact
  obtain ⟨x, hx⟩ := hcompact.exists_isGreatest hne
  have hxeq : Φ x = a := hx.1
  have hx0 : 0 < x := by
    by_contra hn
    have hz : x = 0 := le_antisymm (le_of_not_gt hn) bot_le
    rw [hz, hΦ.zero] at hxeq
    exact (ne_of_gt ha) hxeq.symm
  have hxtop : x ≠ ∞ := by
    intro ht
    rw [ht] at hxeq
    exact (ne_of_lt hatop) hxeq.symm
  refine ⟨x, hx0, hxtop, hxeq, ?_⟩
  intro y
  constructor
  · intro hy
    by_contra hn
    have hm := hΦ.mono (le_of_not_gt hn)
    rw [hxeq] at hm
    exact (not_le_of_gt hy) hm
  · intro hy
    by_contra hn
    have he : Φ y = a := le_antisymm (le_of_not_gt hn) (by
      simpa only [hxeq] using hΦ.mono hy.le)
    exact (not_le_of_gt hy) (hx.2 he)

lemma phi_growth_iterate {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0}
    (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c) (k : ℕ) (x : ℝ≥0∞) :
    Φ (2 ^ k * x) ≤ (c : ℝ≥0∞) ^ k * Φ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      Φ (2 ^ (k + 1) * x) = Φ (2 * (2 ^ k * x)) := by congr 1; ring
      _ ≤ (c : ℝ≥0∞) * Φ (2 ^ k * x) := hΦ.growth _
      _ ≤ (c : ℝ≥0∞) * ((c : ℝ≥0∞) ^ k * Φ x) := mul_le_mul' le_rfl ih
      _ = (c : ℝ≥0∞) ^ (k + 1) * Φ x := by ring

end BurkholderDFI.Brownian.Fresh
end

section

open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma uniform_phi_constants (c : ℝ≥0) :
    ∃ γ δ η : ℝ≥0, 1 ≤ γ ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < η ∧
      γ * (4 * δ) ≤ 1 / 2 ∧
      ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
        (∀ x, Φ (2 * x) ≤ (γ : ℝ≥0∞) * Φ x) ∧
        (∀ x, Φ x ≤ (η : ℝ≥0∞) * Φ ((δ : ℝ≥0∞) * x)) := by
  let γ : ℝ≥0 := max c 1
  have hg1 : 1 ≤ γ := le_max_right _ _
  have hgpos : 0 < γ := lt_of_lt_of_le (by norm_num) hg1
  obtain ⟨k, hk⟩ := exists_nat_gt (8 * (γ : ℝ))
  have hkpow : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast k.lt_two_pow_self
  have hpow : 8 * γ ≤ (2 : ℝ≥0) ^ k := by
    exact_mod_cast (show 8 * (γ : ℝ) ≤ (2 : ℝ) ^ k by linarith)
  let δ : ℝ≥0 := ((2 : ℝ≥0) ^ k)⁻¹
  let η : ℝ≥0 := γ ^ k
  have hdpos : 0 < δ := inv_pos.mpr (pow_pos (by norm_num) _)
  have hdone : δ ≤ 1 := inv_le_one₀ (pow_pos (by norm_num) k) |>.mpr
    (one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2))
  have hepos : 0 < η := pow_pos hgpos _
  have hsmall : γ * (4 * δ) ≤ 1 / 2 := by
    change γ * (4 * ((2 : ℝ≥0) ^ k)⁻¹) ≤ 1 / 2
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_div, NNReal.coe_one]
    have hp : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
    have hb : 8 * (γ : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hpow
    have hi : (2 : ℝ) ^ k * ((2 : ℝ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
    have hm := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hp.le)
    nlinarith
  refine ⟨γ, δ, η, hg1, hdpos, hdone, hepos, hsmall, ?_⟩
  intro Φ hΦ
  have hγ : BurkholderDFI.SquareFnLp.IsPhi Φ γ := by
    refine ⟨hΦ.mono, hΦ.cont, hΦ.zero, ?_⟩
    intro x
    exact (hΦ.growth x).trans (mul_le_mul' (by exact_mod_cast le_max_left c 1) le_rfl)
  refine ⟨hγ.growth, ?_⟩
  intro x
  have h := phi_growth_iterate hγ k ((δ : ℝ≥0∞) * x)
  have he : (2 : ℝ≥0∞) ^ k * (δ : ℝ≥0∞) = 1 := by
    dsimp [δ]
    rw [ENNReal.coe_inv (pow_ne_zero _ (by norm_num)), ENNReal.coe_pow]
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ (by norm_num)) (by finiteness)
  simpa only [← mul_assoc, he, one_mul, η, ENNReal.coe_pow] using h

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma phi_goodlambda_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ≥0∞) (γ δ η ε : ℝ≥0) (hγ : 1 ≤ γ)
    (htail : ∀ r : ℝ, 0 < r →
      P {ω | 2 * ENNReal.ofReal r < g ω ∧ f ω ≤ (δ : ℝ≥0∞) * ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < g ω})
    (Φ : ℝ≥0∞ → ℝ≥0∞) {c : ℝ≥0} (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (hgrowth : ∀ x, Φ (2 * x) ≤ (γ : ℝ≥0∞) * Φ x)
    (hscale : ∀ x, Φ x ≤ (η : ℝ≥0∞) * Φ ((δ : ℝ≥0∞) * x))
    (r : ℝ) (hr : 0 < r) :
    P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < Φ (g ω) ∧
      (2 * (η : ℝ≥0∞)) * Φ (f ω) ≤ ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < Φ (g ω)} := by
  have ha : 0 < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  by_cases hrange : ENNReal.ofReal r < Φ ∞
  · obtain ⟨x, hx0, hxtop, hxeq, hlevel⟩ :=
      phi_rightmost_level hΦ (ENNReal.ofReal r) ha hrange
    have hxreal : 0 < x.toReal := ENNReal.toReal_pos hx0.ne' hxtop
    have hbase := htail x.toReal hxreal
    rw [ENNReal.ofReal_toReal hxtop] at hbase
    have hsub : {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < Φ (g ω) ∧
        (2 * (η : ℝ≥0∞)) * Φ (f ω) ≤ ENNReal.ofReal r} ⊆
        {ω | 2 * x < g ω ∧ f ω ≤ (δ : ℝ≥0∞) * x} := by
      intro ω hω
      constructor
      · by_contra hn
        have hm := (hΦ.mono (le_of_not_gt hn)).trans (hgrowth x)
        rw [hxeq] at hm
        exact (not_le_of_gt hω.1) hm
      · by_contra hn
        have hm : ENNReal.ofReal r ≤ (η : ℝ≥0∞) * Φ (f ω) := by
          rw [← hxeq]
          exact (hscale x).trans (mul_le_mul' le_rfl (hΦ.mono (le_of_lt (lt_of_not_ge hn))))
        have htwice := mul_le_mul' (show (2 : ℝ≥0∞) ≤ 2 from le_rfl) hm
        have hstrict : ENNReal.ofReal r < 2 * ENNReal.ofReal r := by
          simpa [mul_comm] using ENNReal.mul_lt_mul_right ha.ne' ENNReal.ofReal_ne_top
            (by norm_num : (1 : ℝ≥0∞) < 2)
        have hbad : 2 * ENNReal.ofReal r ≤ ENNReal.ofReal r := by
          exact htwice.trans (by simpa only [mul_assoc] using hω.2)
        exact (not_le_of_gt hstrict) hbad
    have he : {ω | x < g ω} = {ω | ENNReal.ofReal r < Φ (g ω)} := by
      ext ω
      exact (hlevel (g ω)).symm
    rw [he] at hbase
    exact (measure_mono hsub).trans hbase
  · have hempty : {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < Φ (g ω) ∧
        (2 * (η : ℝ≥0∞)) * Φ (f ω) ≤ ENNReal.ofReal r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hgr : ENNReal.ofReal r ≤ (γ : ℝ≥0∞) * ENNReal.ofReal r := by
        simpa using mul_le_mul' (show (1 : ℝ≥0∞) ≤ γ by exact_mod_cast hγ)
          (show ENNReal.ofReal r ≤ ENNReal.ofReal r from le_rfl)
      exact (not_le_of_gt hω.1) ((hΦ.mono le_top).trans ((le_of_not_gt hrange).trans hgr))
    rw [hempty, measure_empty]
    exact bot_le

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma ennreal_tail_length (y : ℝ≥0∞) :
    (∫⁻ r : ℝ in Ioi 0, if ENNReal.ofReal r < y then 1 else 0) = y := by
  by_cases hy : y = ∞
  · subst y
    simp [Real.volume_Ioi]
  · calc
      _ = ∫⁻ r : ℝ in Ioi 0, if r < y.toReal then 1 else 0 := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        simp only [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hr) hy]
      _ = ∫⁻ r : ℝ in Ioi 0, (Iio y.toReal).indicator (fun _ => (1 : ℝ≥0∞)) r := by
        rfl
      _ = y := by
        rw [lintegral_indicator measurableSet_Iio]
        rw [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, Measure.restrict_apply measurableSet_Iio]
        have he : Iio y.toReal ∩ Ioi (0 : ℝ) = Ioo 0 y.toReal := by
          ext r
          simp [and_comm]
        rw [he, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hy]

lemma ennreal_lintegral_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y) :
    (∫⁻ ω, Y ω ∂P) = ∫⁻ r : ℝ in Ioi 0, P {ω | ENNReal.ofReal r < Y ω} := by
  have hm : Measurable (fun p : Ω × ℝ =>
      if ENNReal.ofReal p.2 < Y p.1 then (1 : ℝ≥0∞) else 0) := by
    apply Measurable.ite
    · exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        (hY.comp measurable_fst)
    · exact measurable_const
    · exact measurable_const
  calc
    _ = ∫⁻ ω, (∫⁻ r : ℝ in Ioi 0,
        if ENNReal.ofReal r < Y ω then 1 else 0) ∂P := by
      apply lintegral_congr
      intro ω
      exact (ennreal_tail_length (Y ω)).symm
    _ = ∫⁻ r : ℝ in Ioi 0, ∫⁻ ω,
        if ENNReal.ofReal r < Y ω then 1 else 0 ∂P :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro r
      have hs : MeasurableSet {ω | ENNReal.ofReal r < Y ω} :=
        measurableSet_lt measurable_const hY
      have he : (fun ω => if ENNReal.ofReal r < Y ω then (1 : ℝ≥0∞) else 0) =
          ({ω | ENNReal.ofReal r < Y ω}).indicator (fun _ => 1) := by
        funext ω
        simp [Set.indicator]
      rw [he, lintegral_indicator hs]
      simp

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma measurable_tail_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ≥0∞) :
    Measurable (fun r : ℝ => P {ω | ENNReal.ofReal r < Y ω}) := by
  apply Antitone.measurable
  intro a b hab
  apply measure_mono
  intro ω hω
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hω

lemma ennreal_absorb_half (A B : ℝ≥0∞) (a : ℝ≥0) (hA : A ≠ ∞)
    (ha : a ≤ 1 / 2) (h : A ≤ (a : ℝ≥0∞) * A + B) : A ≤ 2 * B := by
  by_cases hB : B = ∞
  · simp [hB]
  · have hfin : (a : ℝ≥0∞) * A + B ≠ ∞ := by finiteness
    have ht := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_add (by finiteness) hB, ENNReal.toReal_mul, ENNReal.coe_toReal] at ht
    have har : (a : ℝ) ≤ 1 / 2 := by exact_mod_cast ha
    have hb : A.toReal ≤ 2 * B.toReal := by
      nlinarith [ENNReal.toReal_nonneg (a := A), ENNReal.toReal_nonneg (a := B)]
    apply (ENNReal.toReal_le_toReal hA (by finiteness)).mp
    simpa using hb

lemma goodlambda_total_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U W : Ω → ℝ≥0∞) (γ ε : ℝ≥0)
    (hbad : ∀ r : ℝ, 0 < r →
      P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω ∧ W ω ≤ ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω})
    (r : ℝ) (hr : 0 < r) :
    P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω} ≤
      (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω} + P {ω | ENNReal.ofReal r < W ω} := by
  have hsub : {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω} ⊆
      {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω ∧ W ω ≤ ENNReal.ofReal r} ∪
      {ω | ENNReal.ofReal r < W ω} := by
    intro ω hω
    by_cases hw : W ω ≤ ENNReal.ofReal r
    · exact Or.inl ⟨hω, hw⟩
    · exact Or.inr (lt_of_not_ge hw)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (hbad r hr) le_rfl))

lemma scaled_expectation_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (U W : Ω → ℝ≥0∞)
    (hU : Measurable U) (hW : Measurable W) (γ ε : ℝ≥0) (hγ : 0 < γ)
    (htail : ∀ r : ℝ, 0 < r →
      P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω} + P {ω | ENNReal.ofReal r < W ω}) :
    (∫⁻ ω, U ω ∂P) / (γ : ℝ≥0∞) ≤
      (ε : ℝ≥0∞) * (∫⁻ ω, U ω ∂P) + ∫⁻ ω, W ω ∂P := by
  have hg0 : (γ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hγ.ne'
  calc
    _ = ∫⁻ ω, U ω / (γ : ℝ≥0∞) ∂P := by
      simp only [div_eq_mul_inv, lintegral_mul_const _ hU]
    _ = ∫⁻ r : ℝ in Ioi 0, P {ω | ENNReal.ofReal r < U ω / (γ : ℝ≥0∞)} :=
      ennreal_lintegral_tail P _ (hU.div_const _)
    _ ≤ ∫⁻ r : ℝ in Ioi 0,
        ((ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω} + P {ω | ENNReal.ofReal r < W ω}) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have he : {ω | ENNReal.ofReal r < U ω / (γ : ℝ≥0∞)} =
          {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω} := by
        ext ω
        change ENNReal.ofReal r < U ω / (γ : ℝ≥0∞) ↔ (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl hg0) (Or.inl ENNReal.coe_ne_top)]
        rw [mul_comm]
      rw [he]
      exact htail r hr
    _ = _ := by
      have hm : Measurable (fun r : ℝ => (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω}) :=
        measurable_const.mul (measurable_tail_measure P U)
      calc
        _ = (∫⁻ r : ℝ in Ioi 0, (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω}) +
            ∫⁻ r : ℝ in Ioi 0, P {ω | ENNReal.ofReal r < W ω} := by
          simpa only [Pi.mul_apply] using! lintegral_add_left hm
            (fun r : ℝ => P {ω | ENNReal.ofReal r < W ω})
        _ = _ := by
          rw [lintegral_const_mul _ (measurable_tail_measure P U),
            ← ennreal_lintegral_tail P U hU, ← ennreal_lintegral_tail P W hW]

lemma goodlambda_finite_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (U W : Ω → ℝ≥0∞)
    (hU : Measurable U) (hW : Measurable W) (γ ε : ℝ≥0) (hγ : 0 < γ)
    (hsmall : γ * ε ≤ 1 / 2) (hfinite : (∫⁻ ω, U ω ∂P) ≠ ∞)
    (hbad : ∀ r : ℝ, 0 < r →
      P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω ∧ W ω ≤ ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω}) :
    (∫⁻ ω, U ω ∂P) ≤ (2 * (γ : ℝ≥0∞)) * ∫⁻ ω, W ω ∂P := by
  have h := scaled_expectation_of_tail P U W hU hW γ ε hγ (goodlambda_total_tail P U W γ ε hbad)
  have hm := mul_le_mul' (show (γ : ℝ≥0∞) ≤ γ from le_rfl) h
  rw [ENNReal.mul_div_cancel (by exact_mod_cast hγ.ne') ENNReal.coe_ne_top, mul_add] at hm
  have hb : (∫⁻ ω, U ω ∂P) ≤ ((γ * ε : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, U ω ∂P) +
      (γ : ℝ≥0∞) * ∫⁻ ω, W ω ∂P := by
    simpa only [ENNReal.coe_mul, mul_assoc] using hm
  have hh := ennreal_absorb_half _ _ (γ * ε) hfinite hsmall hb
  simpa only [mul_assoc] using hh

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

lemma goodlambda_truncate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U W : Ω → ℝ≥0∞) (γ ε : ℝ≥0) (hγ : 1 ≤ γ)
    (hbad : ∀ r : ℝ, 0 < r →
      P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω ∧ W ω ≤ ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω})
    (N : ℝ≥0∞) (r : ℝ) (hr : 0 < r) :
    P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < min (U ω) N ∧ W ω ≤ ENNReal.ofReal r} ≤
      (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < min (U ω) N} := by
  by_cases hn : (γ : ℝ≥0∞) * ENNReal.ofReal r < N
  · have hrN : ENNReal.ofReal r < N := lt_of_le_of_lt (by
      simpa using mul_le_mul' (show (1 : ℝ≥0∞) ≤ γ by exact_mod_cast hγ)
        (show ENNReal.ofReal r ≤ ENNReal.ofReal r from le_rfl)) hn
    have he : {ω | ENNReal.ofReal r < min (U ω) N} = {ω | ENNReal.ofReal r < U ω} := by
      ext ω
      simp [hrN]
    rw [he]
    apply le_trans (measure_mono ?_) (hbad r hr)
    intro ω hω
    exact ⟨lt_of_lt_of_le hω.1 (min_le_left _ _), hω.2⟩
  · have he : {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < min (U ω) N ∧
        W ω ≤ ENNReal.ofReal r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hn (lt_of_lt_of_le hω.1 (min_le_right _ _))
    rw [he, measure_empty]
    exact bot_le

lemma ennreal_iSup_min_nat (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  rw [← inf_iSup_eq, ENNReal.iSup_natCast]
  simp

lemma goodlambda_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U W : Ω → ℝ≥0∞)
    (hU : Measurable U) (hW : Measurable W) (γ ε : ℝ≥0) (hγ : 1 ≤ γ)
    (hsmall : γ * ε ≤ 1 / 2)
    (hbad : ∀ r : ℝ, 0 < r →
      P {ω | (γ : ℝ≥0∞) * ENNReal.ofReal r < U ω ∧ W ω ≤ ENNReal.ofReal r} ≤
        (ε : ℝ≥0∞) * P {ω | ENNReal.ofReal r < U ω}) :
    (∫⁻ ω, U ω ∂P) ≤ (2 * (γ : ℝ≥0∞)) * ∫⁻ ω, W ω ∂P := by
  have htrunc : ∀ n : ℕ, (∫⁻ ω, min (U ω) (n : ℝ≥0∞) ∂P) ≤
      (2 * (γ : ℝ≥0∞)) * ∫⁻ ω, W ω ∂P := by
    intro n
    have hfin : (∫⁻ ω, min (U ω) (n : ℝ≥0∞) ∂P) ≠ ∞ := by
      have hle : (∫⁻ ω, min (U ω) (n : ℝ≥0∞) ∂P) ≤ n := by
        calc
          _ ≤ ∫⁻ _ : Ω, (n : ℝ≥0∞) ∂P := lintegral_mono (fun _ => min_le_right _ _)
          _ = n := by simp
      exact ne_top_of_le_ne_top (by finiteness) hle
    exact goodlambda_finite_expectation P (fun ω => min (U ω) n) W
      (hU.min measurable_const) hW γ ε (lt_of_lt_of_le (by norm_num) hγ)
      hsmall hfin (goodlambda_truncate P U W γ ε hγ hbad n)
  calc
    _ = ∫⁻ ω, ⨆ n : ℕ, min (U ω) (n : ℝ≥0∞) ∂P := by
      simp only [ennreal_iSup_min_nat]
    _ = ⨆ n : ℕ, ∫⁻ ω, min (U ω) (n : ℝ≥0∞) ∂P := by
      apply lintegral_iSup (fun _ => hU.min measurable_const)
      intro i j hij ω
      exact min_le_min_left _ (by exact_mod_cast hij)
    _ ≤ _ := iSup_le htrunc

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace BurkholderDFI.Brownian.Fresh

theorem uniform_phi_goodlambda (c : ℝ≥0) :
    ∃ δ C : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (f g : Ω → ℝ≥0∞), Measurable f → Measurable g →
        (∀ r : ℝ, 0 < r →
          P {ω | 2 * ENNReal.ofReal r < g ω ∧ f ω ≤ (δ : ℝ≥0∞) * ENNReal.ofReal r} ≤
            ((4 * δ : ℝ≥0) : ℝ≥0∞) * P {ω | ENNReal.ofReal r < g ω}) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          (∫⁻ ω, Φ (g ω) ∂P) ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (f ω) ∂P := by
  obtain ⟨γ, δ, η, hγ, hd0, hd1, he0, hsmall, hscale⟩ := uniform_phi_constants c
  let C : ℝ≥0 := 4 * γ * η
  have hg0 : 0 < γ := lt_of_lt_of_le (by norm_num) hγ
  refine ⟨δ, C, hd0, hd1, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro Ω _ P _ f g hf hg htail Φ hΦ
    obtain ⟨hgrowth, hinv⟩ := hscale Φ hΦ
    have hF : Measurable (fun ω => Φ (f ω)) := hΦ.cont.measurable.comp hf
    have hG : Measurable (fun ω => Φ (g ω)) := hΦ.cont.measurable.comp hg
    have hW : Measurable (fun ω => (2 * (η : ℝ≥0∞)) * Φ (f ω)) := measurable_const.mul hF
    have hb := phi_goodlambda_tail P f g γ δ η (4 * δ) hγ htail Φ hΦ hgrowth hinv
    have h := goodlambda_expectation P (fun ω => Φ (g ω))
      (fun ω => (2 * (η : ℝ≥0∞)) * Φ (f ω)) hG hW γ (4 * δ) hγ hsmall hb
    rw [lintegral_const_mul _ hF] at h
    have he : (2 * (γ : ℝ≥0∞)) * (2 * (η : ℝ≥0∞)) = (C : ℝ≥0∞) := by
      simp only [C, ENNReal.coe_mul, ENNReal.coe_ofNat]
      ring
    simpa only [← mul_assoc, he] using h

end BurkholderDFI.Brownian.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.Brownian.Fresh

/-- Theorem 6.1, (6.2), p. 25: `c EΦ(τ^{1/2}) ≤ EΦ(X*(τ)) ≤ C EΦ(τ^{1/2})` for every stopping
time `τ` of Brownian motion, with `c, C` depending only on the growth constant of (6.1). -/
theorem native_theorem_6_1 (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → ℝ), IsBM X P → ∀ τ : Ω → ℝ≥0∞, IsStoppingTimeOf X τ →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P ≤ ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ∧
          ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P := by
  obtain ⟨δ, C, hd0, hd1, hC, hb⟩ := uniform_phi_goodlambda c
  refine ⟨C⁻¹, C, inv_pos.mpr hC, hC, ?_⟩
  intro Ω _ P _ X hX τ hτ Φ hΦ
  have ht : Measurable τ := stopping_measurable hX.2.1 hτ
  have hg : Measurable (fun ω => (τ ω)^(1/2 : ℝ)) := ht.pow_const _
  have hf : Measurable (fun ω => maxStopped X (τ ω) ω) :=
    measurable_maxStopped hX.2.2 hX.2.1 ht
  have hl := hb Ω P (fun ω => maxStopped X (τ ω) ω) (fun ω => (τ ω)^(1/2 : ℝ)) hf hg
    (fun r hr => by
      simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat] using lower_good_lambda hX hτ δ hr) Φ hΦ
  have hu := hb Ω P (fun ω => (τ ω)^(1/2 : ℝ)) (fun ω => maxStopped X (τ ω) ω) hg hf
    (fun r hr => by
      simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat] using upper_good_lambda hX hτ δ hd1 hr) Φ hΦ
  refine ⟨?_, hu⟩
  calc
    (↑C⁻¹ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω^(1/2 : ℝ)) ∂P
        ≤ (↑C⁻¹ : ℝ≥0∞) * ((C : ℝ≥0∞) * ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P) :=
      mul_le_mul' le_rfl hl
    _ = _ := by
      rw [ENNReal.coe_inv hC.ne', ← mul_assoc,
        ENNReal.inv_mul_cancel (by exact_mod_cast hC.ne') ENNReal.coe_ne_top, one_mul]

end BurkholderDFI.Brownian.Fresh
end

open BurkholderDFI.Brownian

theorem solution (c : ℝ≥0) :
    ∃ C₁ C₂ : ℝ≥0, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → ℝ), IsBM X P → ∀ τ : Ω → ℝ≥0∞, IsStoppingTimeOf X τ →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          (C₁ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P ≤ ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ∧
          ∫⁻ ω, Φ (maxStopped X (τ ω) ω) ∂P ≤ (C₂ : ℝ≥0∞) * ∫⁻ ω, Φ (τ ω ^ (1 / 2 : ℝ)) ∂P  := by
  exact Fresh.native_theorem_6_1 c

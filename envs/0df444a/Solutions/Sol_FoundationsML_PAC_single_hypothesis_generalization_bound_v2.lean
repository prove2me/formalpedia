-- Prove2me | solution 1 for FoundationsML.PAC.single_hypothesis_generalization_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:50:42.020468+00:00
-- url     : https://prove2.me/submissions/0139389d-52d1-4ccf-8952-4269a5361337

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace FoundationsML.PAC.SHGB9a

lemma one_sided {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (A : Set X) (hA : MeasurableSet A) (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin m => D)).real
      {S : Fin m → X | (D A).toReal * m - ∑ i, A.indicator (fun _ => (1:ℝ)) (S i) < m * t}ᶜ
      ≤ Real.exp (-2 * m * t ^ 2) := by
  set p : ℝ := (D A).toReal with hp
  set Y : X → ℝ := fun x => p - A.indicator (fun _ => (1:ℝ)) x with hY
  have hYmeas : Measurable Y :=
    measurable_const.sub ((measurable_const).indicator hA)
  have hYint : ∫ x, Y x ∂D = 0 := by
    simp only [hY]
    rw [integral_sub (integrable_const _) ((integrable_const (1:ℝ)).indicator hA),
      integral_const, integral_indicator_const _ hA]
    simp [hp, Measure.real]
  have hYbd : ∀ᵐ x ∂D, Y x ∈ Set.Icc (p - 1) (p - 0) := by
    refine ae_of_all _ (fun x => ?_)
    simp only [hY, Set.mem_Icc]
    by_cases hx : x ∈ A <;> simp [hx]
  have hsubD : HasSubgaussianMGF Y ((‖(p - 0) - (p - 1)‖₊ / 2) ^ 2) D :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hYmeas.aemeasurable hYbd hYint
  have hc : ((‖(p - 0) - (p - 1)‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    have : (p - 0) - (p - 1) = (1:ℝ) := by ring
    rw [this]; simp; norm_num
  rw [hc] at hsubD
  set P := Measure.pi (fun _ : Fin m => D)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun S : Fin m → X => Y (S i)) (1/4) P := by
    intro i _
    have hmap : P.map (Function.eval i) = D := (measurePreserving_eval (fun _ : Fin m => D) i).map_eq
    have := HasSubgaussianMGF.of_map (μ := P) (Y := Function.eval i) (X := Y)
      (measurable_pi_apply i).aemeasurable (by rw [hmap]; exact hsubD)
    exact this
  have hind : iIndepFun (fun (i : Fin m) (S : Fin m → X) => Y (S i)) P :=
    iIndepFun_pi (X := fun _ => Y) (fun _ => hYmeas.aemeasurable)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (ε := m * t) (by positivity)
  refine le_trans (measureReal_mono ?_) (le_trans hH (le_of_eq ?_))
  · intro S hS
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hS
    simp only [Set.mem_setOf_eq, hY]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring

end FoundationsML.PAC.SHGB9a

open MeasureTheory FoundationsML.PAC in
theorem solution
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc_meas : Measurable c) (hh_meas : Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c h ≤
        EmpiricalError S c h + Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by
  set A : Set X := {x | h x ≠ c x} with hAdef
  have hA : MeasurableSet A := (measurableSet_eq_fun hh_meas hc_meas).compl
  set t : ℝ := Real.sqrt (Real.log (2 / δ) / (2 * m)) with htdef
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (2 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]; linarith
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = Real.log (2 / δ) / (2 * m) := by
    rw [htdef, Real.sq_sqrt]; positivity
  have key := FoundationsML.PAC.SHGB9a.one_sided D A hA m hm t ht0
  have hexp : Real.exp (-2 * m * t ^ 2) = δ / 2 := by
    rw [ht2]
    have : -2 * (m:ℝ) * (Real.log (2 / δ) / (2 * m)) = - Real.log (2 / δ) := by
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexp] at key
  set P := Measure.pi (fun _ : Fin m => D)
  set G := {S : Fin m → X | FoundationsML.PAC.GeneralizationError D c h ≤
        FoundationsML.PAC.EmpiricalError S c h + t}
  set B := {S : Fin m → X | (D A).toReal * m - ∑ i, A.indicator (fun _ => (1:ℝ)) (S i) < m * t}
  have hBG : B ⊆ G := by
    intro S hS
    simp only [B, G, Set.mem_setOf_eq] at hS ⊢
    have hle : (D A).toReal ≤ (∑ i, A.indicator (fun _ => (1:ℝ)) (S i)) / m + t := by
      rw [div_add' _ _ _ hmR.ne', le_div_iff₀ hmR]
      linarith
    unfold FoundationsML.PAC.GeneralizationError FoundationsML.PAC.EmpiricalError
    convert hle using 3
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hx : h (S i) = c (S i) <;> simp [Set.indicator, hAdef, hx]
  have hcompl : P.real Gᶜ ≤ δ / 2 :=
    le_trans (measureReal_mono (Set.compl_subset_compl.mpr hBG)) key
  have hu : (1:ℝ) ≤ P.real G + P.real Gᶜ := by
    have := measureReal_union_le (μ := P) G Gᶜ
    rw [Set.union_compl_self, probReal_univ] at this
    exact this
  show 1 - δ ≤ P.real G
  linarith

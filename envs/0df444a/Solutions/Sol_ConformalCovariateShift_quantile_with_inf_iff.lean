-- Prove2me | solution 1 for ConformalCovariateShift.quantile_with_inf_iff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:41:27.543178+00:00
-- url     : https://prove2.me/submissions/5821d567-d4a6-4346-9e42-02f5b841b5ba

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

lemma qi_meas_eq {n : ℕ} (v : Fin (n + 1) → ℝ) (z : EReal) (hz : z < (v (Fin.last n) : EReal)) :
    augDist (fun _ => 1 / ((n : ℝ) + 1)) v (Set.Iic z) =
      discreteDist (fun _ => 1 / ((n : ℝ) + 1)) (fun i => (v i : EReal)) (Set.Iic z) := by
  unfold augDist discreteDist
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  split_ifs with h
  · subst h
    have h1 : (⊤ : EReal) ∉ Set.Iic z := by
      simp only [Set.mem_Iic, top_le_iff]; rintro rfl; exact absurd hz (by simp)
    have h2 : ((v (Fin.last n) : ℝ) : EReal) ∉ Set.Iic z := by
      simp only [Set.mem_Iic, not_le]; exact hz
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  · rfl

theorem quantile_with_inf_iff {n : ℕ} (v : Fin (n + 1) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (v (Fin.last n) : EReal) ≤ quantileWithInf β v ↔ (v (Fin.last n) : EReal) ≤ empQuantile β v := by
  unfold quantileWithInf empQuantile quantile
  rw [le_sInf_iff, le_sInf_iff]
  constructor
  · intro h z hz
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (h z (by simp only [Set.mem_setOf_eq] at hz ⊢; rw [qi_meas_eq v z hlt]; exact hz)) (not_le.mpr hlt)
  · intro h z hz
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (h z (by simp only [Set.mem_setOf_eq] at hz ⊢; rw [← qi_meas_eq v z hlt]; exact hz)) (not_le.mpr hlt)

end ConformalCovariateShift
open ConformalCovariateShift in
theorem solution {n : ℕ} (v : Fin (n + 1) → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (v (Fin.last n) : EReal) ≤ quantileWithInf β v ↔ (v (Fin.last n) : EReal) ≤ empQuantile β v :=
  quantile_with_inf_iff v β hβ0 hβ1

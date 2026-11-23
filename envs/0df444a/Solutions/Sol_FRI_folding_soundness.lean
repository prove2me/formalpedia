-- Prove2me | solution 1 for FRI_folding_soundness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:53.051178+00:00
-- url     : https://prove2.me/submissions/21077e6a-8e24-4a5b-85d1-b7306d9abb9e

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_folding_preserves_agreement
import Theorems.Thm_FRI_BadEvent_eq_FoldingBadEvent
import Theorems.Thm_FRI_degree_succ_eq
import Theorems.Thm_uniform_measure_eq_card_div


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : FRI_MCA_Hypothesis P bound errorstar)
    (f_0 : P.D_0 → F)
    (i : Fin P.num_foldings)
    (f_prev : FRI_domain P i → F)
    (h_deg : FRI_degree P i ≥ P.m i)
    (h_foldable : IsFoldable (FRI_domain P i) (P.m i))
    (h_delta_nonneg : 0 ≤ FRI_distance_star P f_0 bound)
    (h_delta_lt : FRI_distance_star P f_0 bound < 1 - bound)
    (h_error_nonneg : 0 ≤ FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound)) :
    FRI_BadEvent_Prob P f_0 bound i f_prev ≤
      FRI_error_fold P bound errorstar i (FRI_distance_star P f_0 bound) := by
  unfold FRI_BadEvent_Prob FRI_error_fold at *
  have := @folding_preserves_agreement
  convert this (FRI_domain P i) (P.m i) (FRI_degree P i) ?_ ?_ h_foldable bound errorstar ?_
    (extend_by_zero (FRI_domain P i) f_prev) (FRI_distance_star P f_0 bound)
    h_delta_nonneg h_delta_lt using 1
  · classical
    rw [uniform_measure_eq_card_div, ENNReal.le_ofReal_iff_toReal_le] <;> norm_num
    · congr! 2
      · congr! 2
        ext; simp only [FRI_BadEvent_eq_FoldingBadEvent, Finset.mem_filter, Finset.mem_univ,
          true_and]
        congr! 2
        ext; simp only [Fin.eta, FRI_code_cast, Submodule.mem_map,
          LinearEquiv.funCongrLeft_apply, FRI_code, Fin.is_lt, FRI_degree_succ_eq]
        simp_all only [reedSolomon, ge_iff_le, gt_iff_lt, PMF.toMeasure_apply_fintype,
          Submodule.mem_map, exists_exists_and_eq_and]
        rfl
      · simp_all only [FRI_delta_star, FRI_distance_star, ge_iff_le, gt_iff_lt,
          PMF.toMeasure_apply_fintype, Submodule.carrier_eq_coe, one_div, inf_le_iff,
          tsub_le_iff_right, le_add_iff_nonneg_right, inv_nonneg, Nat.cast_nonneg, or_true,
          inf_of_le_left]
    · simp [ENNReal.div_eq_top]
    · convert h_error_nonneg using 1
      simp_all only [FRI_delta_star, FRI_distance_star, ge_iff_le, gt_iff_lt,
        PMF.toMeasure_apply_fintype, Submodule.carrier_eq_coe, one_div, inf_le_iff,
        tsub_le_iff_right, le_add_iff_nonneg_right, inv_nonneg, Nat.cast_nonneg, or_true,
        inf_of_le_left]
  · exact P.h_m_pos i
  · exact h_deg
  · convert h_mca ⟨i, i.isLt⟩ using 1
    · simp [FRI_domain_succ_eq, pow_domain]
    · simp only [Fin.eta, Fin.val_succ, FRI_code, FRI_degree_succ_eq P i (Fin.is_lt i)]
      have hheq : ∀ D₁ D₂ : Finset F, D₁ = D₂ → reedSolomon D₁ (FRI_degree P ↑i / P.m i) ≍ reedSolomon D₂ (FRI_degree P ↑i / P.m i) := by
        rintro D _ rfl; rfl
      exact hheq _ _ (FRI_domain_succ_eq P i (Fin.is_lt i)).symm

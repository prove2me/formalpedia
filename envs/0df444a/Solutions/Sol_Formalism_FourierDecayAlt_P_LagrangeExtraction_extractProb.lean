-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.extractProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:44.587827+00:00
-- url     : https://prove2.me/submissions/1c3caba4-095f-4bfa-acff-fd58eb2ff1bf

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_sum_prod_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_norm_le_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_sum_abs_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution : ExtractProb := by
  intro V _ _ K d s W grid hP hg y₀
  set Pr : ℝ := ∏ a, ∑ i, |lagCo (grid a) i| with hPr
  have hPpos : 0 < Pr := Finset.prod_pos fun a _ => sum_abs_pos (grid a) (hg a)
  have hth : ∀ j, thGrid grid j = (∏ a, |lagCo (grid a) (j a)|) / Pr := by
    intro j; unfold thGrid; rw [Finset.prod_div_distrib]
  have h0 : ∀ j, 0 ≤ thGrid grid j := fun j => by
    rw [hth]; exact div_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg _) hPpos.le
  have h1 : (∑ j, thGrid grid j) = 1 := by
    simp only [hth]
    rw [← Finset.sum_div, sum_prod_abs, div_self hPpos.ne']
  have h3 : (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) := by
    refine (norm_le_sum s W grid hP hg y₀).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hth]; field_simp
  refine ⟨h0, h1, h3, ?_⟩
  have hL : 0 ≤ (∏ a, ‖s a‖) * ‖W 0 y₀‖ :=
    mul_nonneg (Finset.prod_nonneg fun a _ => norm_nonneg _) (norm_nonneg _)
  have hcs : (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 ≤
      (∑ j, thGrid grid j) * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => h0 j)
      (fun j _ => mul_nonneg (h0 j) (sq_nonneg _)) (fun j _ => le_of_eq (by ring))
  rw [h1, one_mul] at hcs
  calc ((∏ a, ‖s a‖) * ‖W 0 y₀‖) ^ 2
      ≤ (Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖)) ^ 2 :=
        pow_le_pow_left₀ hL h3 2
    _ = Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 := mul_pow _ _ _
    _ ≤ Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
end Formalism.FourierDecayAlt.P.LagrangeExtraction

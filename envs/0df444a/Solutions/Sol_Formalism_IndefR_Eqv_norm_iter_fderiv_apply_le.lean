-- Prove2me | solution 1 for Formalism.IndefR.Eqv.norm_iter_fderiv_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.291073+00:00
-- url     : https://prove2.me/submissions/6e670c7f-d8ee-4d96-b04a-2d055243d695

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
import Theorems.Thm_P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) (w y : V) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ φ z w) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) φ y‖ * ‖w‖ := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have e1 : (fun z => fderiv ℝ φ z w) = (ContinuousLinearMap.apply ℝ ℂ w) ∘ fderiv ℝ φ := rfl
  rw [e1]
  refine ((ContinuousLinearMap.apply ℝ ℂ w).norm_iteratedFDeriv_comp_left hf.contDiffAt
    (natCast_lt_inf' n).le).trans ?_
  have hA : ‖ContinuousLinearMap.apply ℝ ℂ w‖ ≤ ‖w‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm w
  rw [norm_iteratedFDeriv_fderiv]
  calc _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (n + 1) φ y‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = _ := mul_comm _ _
end Formalism.IndefR.Eqv

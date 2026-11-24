-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:10.908865+00:00
-- url     : https://prove2.me/submissions/8cedbb30-1476-4008-913d-c7706c92a8fc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_norm_wirtL_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) {j : ℕ} (hj : j ≤ n)
    (x : Fin d → ℂ) : ‖iteratedFDeriv ℝ j (wirt k f) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f x‖ := by
  rw [wirt_eq]
  have h1 : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  refine ((wirtL V k).norm_iteratedFDeriv_comp_left (N := n) h1.contDiffAt (by exact_mod_cast hj)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ (j + 1) f x‖ := by gcongr; exact norm_wirtL_le k
    _ = _ := one_mul _
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts

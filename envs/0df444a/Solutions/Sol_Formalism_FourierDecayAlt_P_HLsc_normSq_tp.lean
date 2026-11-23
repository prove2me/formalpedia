-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.normSq_tp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:35.600587+00:00
-- url     : https://prove2.me/submissions/19ccccdf-311d-4d88-989c-5457124929f2

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_ee_mul_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : Fin d → ℝ) :
    ((‖tp B c y‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, ee y (σ - σ') * c σ * starRingEnd ℂ (c σ') := by
  push_cast
  rw [← Complex.mul_conj']
  unfold tp
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun σ' _ => ?_))
  rw [← ee_mul_conj, map_mul]
  ring
end Formalism.FourierDecayAlt.P.HLsc

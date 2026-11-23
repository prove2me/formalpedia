-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.tp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.880907+00:00
-- url     : https://prove2.me/submissions/f48fc9cf-af1a-4bc8-97e9-3b81f3def61a

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous

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
theorem _root_.solution (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (z z₀ : Fin d → ℝ) :
    tp B c (z - z₀) = tp B (fun σ => c σ * ee (-z₀) σ) z := by
  unfold tp
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [mul_assoc]
  congr 1
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.HLsc

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.pk_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.909198+00:00
-- url     : https://prove2.me/submissions/30f0ac5a-3489-407c-bc46-c09f910398c9

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_fac_eq

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
theorem _root_.solution (y : Fin d → ℝ) (m : Fin d → ℤ) : pk (fun j => y j + (m j : ℝ)) = pk y := by
  unfold pk
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [fac_eq, fac_eq, mul_add]
  congr 2
  have := Real.cos_add_int_mul_two_pi (2 * π * y j) (m j)
  rw [← this]; congr 1; ring
end Formalism.FourierDecayAlt.P.HLsc

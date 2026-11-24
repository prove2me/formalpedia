-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.dm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:19:04.5758+00:00
-- url     : https://prove2.me/submissions/8917b455-3e5d-44d8-8d65-bf60fe07f2fd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ V) :
    (∑ i ∈ s, f i).dualMap = ∑ i ∈ s, (f i).dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply, LinearMap.sum_apply, map_sum]
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic

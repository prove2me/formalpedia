-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.prj_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:47.269509+00:00
-- url     : https://prove2.me/submissions/003c4be4-0abb-415e-a1ab-e108799656e6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) :
    prj (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • prj (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prj_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, prj_add, prj_rsmul, ih]
end Formalism.FourierDecayAlt.P.Ux1

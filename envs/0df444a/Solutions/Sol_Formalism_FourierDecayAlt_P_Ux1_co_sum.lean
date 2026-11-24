-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.co_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:46.575635+00:00
-- url     : https://prove2.me/submissions/3c244c53-d568-4e49-9edb-d1767196ce4c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_co_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_co_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_co_zero

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    co (∑ b ∈ s, c b • Z b) i = ∑ b ∈ s, c b * co (Z b) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [co_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, co_add, co_smul, ih]
end Formalism.FourierDecayAlt.P.Ux1

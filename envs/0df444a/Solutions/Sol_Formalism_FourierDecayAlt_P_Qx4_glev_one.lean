-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.glev_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:44.934798+00:00
-- url     : https://prove2.me/submissions/2b61b8a9-df28-4d10-8be0-c45feee730c7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (i : Fin (r + 1)) : (1 : Mx k r) ∈ Glev k r i :=
  ⟨uh_one, fun a _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.uh_inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:22.975776+00:00
-- url     : https://prove2.me/submissions/9030edd6-b38e-447a-a65f-719a2688b96f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_inv_mulVec


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
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {v w : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = w) : g⁻¹ *ᵥ w = v :=
  B2x8.al_inv_mulVec (uh_unit hg) h
end Formalism.FourierDecayAlt.P.Qx4

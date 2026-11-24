-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.uh_herm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:00:39.235819+00:00
-- url     : https://prove2.me/submissions/fafe6d1e-f808-4acc-99d1-3e31c7c60552

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv

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
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) : ⟪g *ᵥ u, v⟫ = ⟪u, g⁻¹ *ᵥ v⟫ := by
  rw [← uh_herm hg u (g⁻¹ *ᵥ v), Matrix.mulVec_mulVec, uh_mul_inv hg, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.Dec.Jx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:42.341287+00:00
-- url     : https://prove2.me/submissions/3c60877e-3478-4896-8002-eee5b6c44dff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_iH_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx4_inv_inv__225f23d156f5
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_cF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_uL_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_uL_iH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_rho_eq

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
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.Qx4
namespace Dec
theorem _root_.solution {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') (z z' : Fin (2 * r + k + 1) → ℂ) (φ : ℂ → ℂ)
    (Ψ : Mx k r → (Wq →L[ℂ] Wp)) :
    Jx k r l z z' φ Ψ g = (psi k r z cStd u * psi k r z' cStd u') • (φ c • Ψ g₁) := by
  unfold Jx
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]
end Dec
end Formalism.FourierDecayAlt.P.Qx4

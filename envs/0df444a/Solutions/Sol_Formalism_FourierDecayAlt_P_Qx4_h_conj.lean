-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.h_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:17.080318+00:00
-- url     : https://prove2.me/submissions/d6413f58-eea0-4fa1-972c-7b849697f5f6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_conj


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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (hH : Hᴴ = H) (u v : Fin n → ℂ) : conj (herm H u v) = herm H v u := B2x8.herm_conj H hH u v
end Formalism.FourierDecayAlt.P.Qx4

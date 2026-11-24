-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:05:46.115312+00:00
-- url     : https://prove2.me/submissions/4b46add5-d983-42ff-9ee1-9d354f57fd48

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_mat_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_mat_ext


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
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B := B2x6.mat_ext h
end Formalism.FourierDecayAlt.P.Qx4

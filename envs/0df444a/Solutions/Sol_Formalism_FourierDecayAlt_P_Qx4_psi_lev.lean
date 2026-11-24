-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.psi_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:36.069645+00:00
-- url     : https://prove2.me/submissions/e47f1f7f-4cdc-4d85-a276-24cec38a8079

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_ell_lev

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
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution (z : Fin (2 * r' + k + 1) → ℂ) (c : ℂ) (g : Mx k r') :
    psi k (1 + r') (liftVec k 1 r' z) c (ιLev k 1 r' g) = psi k r' z c g := by
  unfold psi; rw [ell_lev]
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.smM_uL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:24.105865+00:00
-- url     : https://prove2.me/submissions/9aa49e2c-517f-45e9-91f6-4d6e4ce8d3cd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_cF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_hx

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {f : X → Mx k r} {s : Set X} (hf : SmM f s) (h0 : ∀ x ∈ s, cF k r l (f x) ≠ 0) :
    SmM (fun x => uL k r l (f x)) s :=
  smM_hx (smV_smul ((sm_cF hf).inv h0) (smV_mulVec hf (smV_const _ s)))
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.smM_hx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:29:40.345365+00:00
-- url     : https://prove2.me/submissions/eab4dbfa-c9b7-4b32-898b-1e8302f3a22a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smV_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_hs

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
theorem _root_.solution {x : X → Fin (2 * r + k + 1) → ℂ} {s : Set X} (hx' : SmV x s) : SmM (fun y => hx k r l (x y)) s :=
  smM_hs _ (smV_const _ s)
    (smV_sub (smV_sub hx' (smV_const _ s)) (smV_smul (sm_herm _ hx' (smV_const _ s)) (smV_const _ s)))
    (sm_herm _ hx' (smV_const _ s))
end Formalism.FourierDecayAlt.P.Qx4

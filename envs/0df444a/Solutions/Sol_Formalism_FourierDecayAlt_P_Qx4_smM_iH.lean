-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.smM_iH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:10.879228+00:00
-- url     : https://prove2.me/submissions/0b530d9c-8969-4dad-b6bf-151317abb162

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_conjT

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
theorem _root_.solution {f : X → Mx k r} {s : Set X} (hf : SmM f s) : SmM (fun x => iH (f x)) s :=
  smM_mul (smM_mul (smM_const _ s) (smM_conjT hf)) (smM_const _ s)
end Formalism.FourierDecayAlt.P.Qx4

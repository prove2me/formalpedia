-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.smM_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:51:51.47096+00:00
-- url     : https://prove2.me/submissions/ae85aba1-885b-4e50-91b4-2e9df74432af

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_iH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_sm_cF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smM_uL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_smooth_map_weyl_cell
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero


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
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution : SmM (rho k r l) (C0 k r l) := by
  have h1 := smM_id (C0 k r l)
  have h2 : SmM (fun g => uL k r l g) (C0 k r l) := smM_uL h1 fun x hx => hx.1
  have h3 : SmM (fun g => uL k r l (iH g)) (C0 k r l) := smM_uL (smM_iH h1) fun x hx => hx.2
  exact smM_mul (smM_mul (smM_mul (smooth_map_weyl_cell (sm_conj (sm_cF h1)) fun x hx => (map_ne_zero _).2 hx.1) (smM_iH h2)) h1) h3
end Formalism.FourierDecayAlt.P.Qx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.Dec.uL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:20.642783+00:00
-- url     : https://prove2.me/submissions/d45438bc-df6d-4a0b-bdff-a96a3a7a7ac4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_up_hx
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_act_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_cF_eq

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
namespace Dec
theorem _root_.solution {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : uL k r l g = u := by
  unfold uL
  rw [h.cF_eq, h.act_e, smul_smul, inv_mul_cancel₀ h.hc, one_smul, up_hx h.hu]
end Dec
end Formalism.FourierDecayAlt.P.Qx4

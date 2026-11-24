-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.Dec.uL_iH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:27.073862+00:00
-- url     : https://prove2.me/submissions/f32d427c-f142-47ed-8692-817022fe4f4b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_iH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_Dec_uL_eq

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
theorem _root_.solution {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : uL k r l (iH g) = u'⁻¹ := by
  rw [iH_eq h.mem.1, h.inv.uL_eq]
end Dec
end Formalism.FourierDecayAlt.P.Qx4

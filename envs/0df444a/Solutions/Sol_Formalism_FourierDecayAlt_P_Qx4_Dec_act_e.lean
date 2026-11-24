-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.Dec.act_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:51.566641+00:00
-- url     : https://prove2.me/submissions/fd780f92-51ad-4295-9627-930d1c36bcb0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_succ_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_w1_mulVec_bvec_eI

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
theorem _root_.solution {g u g₁ u' : Mx k r} {c : ℂ} (h : Dec k r l g c u g₁ u') : g *ᵥ 𝐞 = c • (u *ᵥ 𝐬) := by
  rw [h.eq, ← Matrix.mulVec_mulVec, h.hu'.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ((glev_succ_iff l g₁).1 h.hg).2.1, w1_mulVec_bvec_eI, Matrix.mulVec_smul]
end Dec
end Formalism.FourierDecayAlt.P.Qx4

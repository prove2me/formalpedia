-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.stab_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:09.012507+00:00
-- url     : https://prove2.me/submissions/b221afe3-1cbe-426c-9465-e369ebc729de

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_succ_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_hx_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_isX_of_glev

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
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r l.castSucc) (he : g *ᵥ 𝐞 = 𝐞) :
    ∃ u ∈ UP k r l, ∃ g₁ ∈ Glev k r l.succ, g = u * g₁ := by
  have hX := isX_of_glev hg he
  have hu := hx_up hX
  refine ⟨hx k r l (g *ᵥ 𝐬), hu, (hx k r l (g *ᵥ 𝐬))⁻¹ * g, ?_, ?_⟩
  · rw [glev_succ_iff]
    refine ⟨glev_mul (glev_inv hu.1) hg, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, he]; exact uh_inv_fix hu.1.1 hu.2.1
    · rw [← Matrix.mulVec_mulVec]; exact uh_inv_fix hu.1.1 (hx_es hX)
  · rw [← Matrix.mul_assoc, uh_mul_inv hu.1.1, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Qx4

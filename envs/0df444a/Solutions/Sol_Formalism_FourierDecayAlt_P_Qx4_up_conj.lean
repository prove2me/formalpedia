-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.up_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:51:41.734414+00:00
-- url     : https://prove2.me/submissions/fe06fb1f-6159-464a-bc32-32939092dccd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_uh_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_glev_succ_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
theorem _root_.solution {u p : Mx k r} (hu : u ∈ UP k r l) (hp : p ∈ Glev k r l.succ) : p * u * p⁻¹ ∈ UP k r l := by
  obtain ⟨hp0, hp1, -⟩ := (glev_succ_iff l p).1 hp
  have hpi : p⁻¹ *ᵥ 𝐞 = 𝐞 := uh_inv_fix hp0.1 hp1
  refine ⟨glev_mul (glev_mul hp0 hu.1) (glev_inv hp0), ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec, hpi, ← Matrix.mulVec_mulVec, hu.2.1, hp1]
  · have h1 : ⟪p⁻¹ *ᵥ y, 𝐞⟫ = 0 := by
      rw [← hpi, uh_herm (uh_inv hp0.1), hy]
    obtain ⟨t, ht⟩ := hu.2.2 _ h1
    refine ⟨t, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_add, Matrix.mulVec_smul, hp1,
      Matrix.mulVec_mulVec, uh_mul_inv hp0.1, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.Qx4

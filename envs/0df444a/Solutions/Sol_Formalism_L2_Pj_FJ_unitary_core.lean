-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.unitary_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:10.398541+00:00
-- url     : https://prove2.me/submissions/4e85deb1-0902-41fb-8bc5-fc4083369a32

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_cM
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_mul
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_transpose
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_add
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hg : (cM g)ᵀ = g) (hiso : Fᵀ * g * cM F = 0)
    (hsk : cM β = -βᵀ) :
    (1 + F * β * (g * cM F)ᵀ)ᵀ * g * cM (1 + F * β * (g * cM F)ᵀ) = g := by
  have hg' : cM g = gᵀ := by
    have := congrArg Matrix.transpose hg
    simpa using this
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, Fᵀ * (g * (cM F * X)) = 0 := by
    intro X
    rw [← Matrix.mul_assoc g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    cM_add, cM_one, cM_mul, cM_transpose, cM_cM, hg', hsk]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul, key, neg_zero, Matrix.mul_zero, add_zero, neg_neg]
  abel
end Formalism.L2.Pj.FJ

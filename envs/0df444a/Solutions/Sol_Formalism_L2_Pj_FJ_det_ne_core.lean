-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.det_ne_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:03.584226+00:00
-- url     : https://prove2.me/submissions/82f3bd0c-a8ab-4280-aede-6ba2e6fe4c25

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

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
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hiso : Fᵀ * g * cM F = 0) :
    (1 + F * β * (g * cM F)ᵀ).det ≠ 0 := by
  have hT : (g * cM F)ᵀ * F = 0 := by
    have := congrArg Matrix.transpose hiso
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  generalize (g * cM F)ᵀ = H at hT ⊢
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, H * (F * X) = 0 := by
    intro X
    rw [← Matrix.mul_assoc, hT, Matrix.zero_mul]
  have hinv : (1 + F * β * H) * (1 - F * β * H) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc, key, Matrix.mul_zero, sub_zero]
    first | abel | skip
  intro h0
  have := congrArg Matrix.det hinv
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this
end Formalism.L2.Pj.FJ

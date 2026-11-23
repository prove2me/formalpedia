-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:35.857705+00:00
-- url     : https://prove2.me/submissions/d09b2170-5060-4380-a109-b24b0af47870

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ m : ℤ, altE H x y = (m : ℝ) := by
  obtain ⟨hpm, hmul⟩ := h.semi
  have hsq : ∀ z ∈ Λ, α z ^ 2 = 1 := by
    intro z hz
    rcases hpm z hz with h' | h' <;> rw [h'] <;> norm_num
  have e := congrArg (· ^ 2) (hmul x hx y hy)
  simp only [mul_pow, hsq x hx, hsq y hy, hsq _ (Λ.add_mem hx hy), one_mul] at e
  rw [sq, ← Complex.exp_add] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e.symm
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h3 : ((altE H x y : ℝ) : ℂ) = ((n : ℤ) : ℂ) := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hpi)
    linear_combination hn
  exact_mod_cast h3
end Formalism.L2.Th1.H

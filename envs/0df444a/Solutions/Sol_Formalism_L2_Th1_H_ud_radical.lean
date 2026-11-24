-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:16.23003+00:00
-- url     : https://prove2.me/submissions/296f52bd-7874-4f02-acc2-a098b085b396

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_mem_latA

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ)
    (hb : ∀ x' ∈ Λ, bC H Ae x x' = 1) : x ∈ latA Λ δ Ae := by
  have hz : Ae.symm x ∈ Λ := by
    have hd : Ae.symm x ∈ dualLat H Λ := by
      show ∀ y ∈ Λ, ∃ m : ℤ, altE H (Ae.symm x) y = (m : ℝ)
      intro y hy
      have e := hb y hy
      unfold bC at e
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e
      refine ⟨-n, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
      have h3 : ((altE H (Ae.symm x) y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hpi
        push_cast
        linear_combination -hn
      exact_mod_cast h3
    have hsd : dualLat H Λ = Λ := h.selfDual
    rw [hsd] at hd
    exact hd
  have hc := h.cay (Ae.symm x)
  rw [LinearEquiv.apply_symm_apply] at hc
  have hw : δ.symm (Ae.symm x) ∈ Λ := by
    have e : δ.symm (Ae.symm x) = Ae.symm x - x :=
      calc δ.symm (Ae.symm x) = Ae.symm x - (Ae.symm x - δ.symm (Ae.symm x)) := by abel
        _ = Ae.symm x - x := by rw [← hc]
    rw [e]
    exact Λ.sub_mem hz hx
  exact mem_latA.mpr ⟨δ.symm (Ae.symm x), hw, by rw [LinearEquiv.apply_symm_apply]; exact hz,
    by rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
end Formalism.L2.Th1.H

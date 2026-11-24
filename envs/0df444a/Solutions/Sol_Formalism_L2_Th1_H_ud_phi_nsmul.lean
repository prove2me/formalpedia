-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_phi_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:36.214282+00:00
-- url     : https://prove2.me/submissions/db55ebe5-7864-479a-88c7-a452e5ad1c32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_re
import Theorems.Thm_Formalism_L2_Th1_H_altE_cayC
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_add
import Theorems.Thm_Formalism_L2_Th1_H_bC_add_left
import Theorems.Thm_Formalism_L2_Th1_H_ud_alpha_nsmul

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ) (k : ℕ) :
    phiC H α Ae (k • x) = phiC H α Ae x ^ (k ^ 2) := by
  have hαsq : α x ^ 2 = 1 := by
    rcases h.semi.1 x hx with h' | h' <;> rw [h'] <;> norm_num
  have h0 : altE H x x = 0 := by
    have hh := congrArg Complex.im (h.herm x x)
    simp only [Complex.conj_im] at hh
    unfold altE
    linarith
  have hHc : H (cayC Ae x) x = Complex.I * (altE H (Ae.symm x) x : ℂ) := by
    apply Complex.ext
    · simp [ud_re h x]
    · have e := altE_cayC (H := H) (Ae := Ae) x x
      rw [h0] at e
      simp only [altE] at e
      simp [e, altE]
  have hsq : phiC H α Ae x ^ 2 = bC H Ae x x := by
    unfold phiC bC
    rw [mul_pow, hαsq, one_mul, ← Complex.exp_nat_mul, hHc]
    congr 1
    push_cast
    ring
  have hbk : ∀ k : ℕ, bC H Ae (k • x) x = bC H Ae x x ^ k := by
    intro k
    induction k with
    | zero => simp [bC, altE]
    | succ k ih => rw [succ_nsmul, bC_add_left, ih, pow_succ]
  induction k with
  | zero =>
    have e := ud_alpha_nsmul h hx 0
    simp only [zero_smul, pow_zero] at e
    simp [phiC, e]
  | succ k ih =>
    have hkx : k • x ∈ Λ := Λ.nsmul_mem hx k
    rw [succ_nsmul, ud_phi_add h hkx hx, ih, hbk k, ← hsq]
    ring
end Formalism.L2.Th1.H

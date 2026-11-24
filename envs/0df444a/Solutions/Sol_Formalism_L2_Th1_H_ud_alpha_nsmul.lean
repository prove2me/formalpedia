-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_alpha_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:32.177525+00:00
-- url     : https://prove2.me/submissions/7ac130e8-5bb0-4f7f-b707-0822064a6a46

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ) (k : ℕ) :
    α (k • x) = α x ^ k := by
  have h0 : (H x x).im = 0 := by
    have hh := congrArg Complex.im (h.herm x x)
    simp only [Complex.conj_im] at hh
    linarith
  induction k with
  | zero =>
    simp only [zero_smul, pow_zero]
    have e := h.semi.2 0 Λ.zero_mem 0 Λ.zero_mem
    rcases h.semi.1 0 Λ.zero_mem with h' | h'
    · exact h'
    · norm_num [altE, h'] at e
  | succ k ih =>
    have hkx : k • x ∈ Λ := Λ.nsmul_mem hx k
    have him : altE H (k • x) x = 0 := by simp [altE, h0]
    rw [succ_nsmul, h.semi.2 _ hkx _ hx, ih, pow_succ, him]
    simp
end Formalism.L2.Th1.H

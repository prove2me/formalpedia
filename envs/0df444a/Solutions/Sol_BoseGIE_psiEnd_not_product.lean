-- Prove2me | solution 1 for BoseGIE.psiEnd_not_product
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:48:55.006603+00:00
-- url     : https://prove2.me/submissions/117c4413-f2e4-48b0-86e4-20bfb6ee6801

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_BoseGIE_defs
set_option autoImplicit false

open Matrix
open scoped Kronecker ComplexOrder
open BoseGIE

theorem solution (α β : ℝ) (h : ∀ n : ℤ, α + β ≠ 2 * Real.pi * n) :
    ¬ IsProductVector (psiEnd α β) := by
  rintro ⟨u, w, huw⟩
  have h00 := huw 0 0
  have h01 := huw 0 1
  have h10 := huw 1 0
  have h11 := huw 1 1
  simp [psiEnd] at h00 h01 h10 h11
  have key : Complex.exp (↑α * Complex.I) * Complex.exp (↑β * Complex.I) = 1 := by
    have h4 : (2⁻¹ : ℂ) * 2⁻¹ = (2⁻¹ * Complex.exp (↑α * Complex.I)) * (2⁻¹ * Complex.exp (↑β * Complex.I)) := by
      rw [h01, h10]
      calc (2⁻¹ : ℂ) * 2⁻¹ = (u 0 * w 0) * (u 1 * w 1) := by rw [← h00, ← h11]
        _ = (u 0 * w 1) * (u 1 * w 0) := by ring
    have h4' : (2⁻¹ : ℂ) * 2⁻¹ ≠ 0 := by norm_num
    apply mul_left_cancel₀ h4'
    linear_combination (-1 : ℂ) * h4
  rw [← Complex.exp_add] at key
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key
  apply h n
  have := congrArg Complex.im hn
  simp at this
  linarith

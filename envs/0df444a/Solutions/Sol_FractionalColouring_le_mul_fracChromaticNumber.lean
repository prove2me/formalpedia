-- Prove2me | solution 1 for FractionalColouring.le_mul_fracChromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:55.043088+00:00
-- url     : https://prove2.me/submissions/7d4e98f9-976b-47a2-ae46-d5941bcea7e5

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_isFracColouring_singletons
public import Theorems.Thm_FractionalColouring_weights_nonempty
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply



set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
namespace FractionalColouring
theorem _root_.solution {a c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, IsFracColouring G x → a ≤ c * ∑ s, x s) : a ≤ c * fracChromaticNumber G := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h _ isFracColouring_singletons
  · rw [← div_le_iff₀' hc]
    exact le_csInf weights_nonempty (by
      rintro _ ⟨x, hx, rfl⟩
      rw [div_le_iff₀' hc]
      exact h x hx)
end FractionalColouring

-- Prove2me | solution 1 for DeciSigma1.Constraints.LabelClash.unsatisfiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:48.961084+00:00
-- url     : https://prove2.me/submissions/7be22b9a-92dc-49ef-989b-bcb92fa092e2

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerF_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerTop_sound
public import Theorems.Thm_DeciSigma1_Constraints_UpperF_sound
public import Theorems.Thm_DeciSigma1_Constraints_UpperBot_sound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace LabelClash
theorem _root_.solution {Γ : List (LitT n V)} (h : LabelClash Γ) :
    ¬ ∃ ρ, Covariant.Sat ρ Γ := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨x, (⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩)⟩ := h
  · exact Tree.top_ne_bot ((hl.sound hρ).symm.trans (hu.sound hρ))
  · exact hu.sound hρ (by rw [hl.sound hρ]; rfl)
  · exact hl.sound hρ (by rw [hu.sound hρ]; rfl)
end LabelClash
end DeciSigma1.Constraints

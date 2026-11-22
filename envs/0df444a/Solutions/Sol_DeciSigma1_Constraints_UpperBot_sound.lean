-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperBot.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:00.965044+00:00
-- url     : https://prove2.me/submissions/809f53d6-9adc-476e-88b6-735e2f734df1

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerF_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerTop_sound
public import Theorems.Thm_DeciSigma1_Constraints_UpperF_sound
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
namespace UpperBot
theorem _root_.solution {Γ : List (LitT n V)} {x : V} {ρ : V → Semantics.Tree n}
    (h : UpperBot Γ x) (hρ : Covariant.Sat ρ Γ) : ρ x = Tree.bot := by
  obtain ⟨v, hl, hd⟩ := h
  have hle := hd.sound ρ hρ
  have hv : ρ v = Tree.bot := hρ _ hl
  rw [hv] at hle
  exact (Tree.le_bot_iff _).mp hle
end UpperBot
end DeciSigma1.Constraints

-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.not_le_iff_unsafe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:18.842956+00:00
-- url     : https://prove2.me/submissions/e7ead50a-3651-4ee1-9da6-1821bf949f39

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_mono
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_eq_top_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_not_hasLabel_of_label
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t u : Tree n) :
    ¬ t ≤ u ↔ ∃ ν, (trace t ν ≠ Tree.bot ∧ trace u ν = Tree.bot) ∨
      (trace t ν = Tree.top ∧ trace u ν ≠ Tree.top) := by
  classical
  constructor
  · intro h
    change ¬ (∀ ν a b, t.fn ν = some a → u.fn ν = some b → a ≤ b) at h
    push Not at h
    obtain ⟨ν, a, b, ht, hu, hab⟩ := h
    have hc : (b = Sym.bot ∧ a ≠ Sym.bot) ∨ (a = Sym.top ∧ b ≠ Sym.top) := by
      cases a <;> cases b <;> first
        | exact Or.inl ⟨rfl, by decide⟩
        | exact Or.inr ⟨rfl, by decide⟩
        | exact absurd hab (by decide)
    refine ⟨ν, ?_⟩
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨fun h => not_hasLabel_of_label ht (by decide) ha
        ((trace_eq_bot_iff _ _).mp h),
        (trace_eq_bot_iff _ _).mpr ⟨ν, List.prefix_refl _, hu⟩⟩
    · exact Or.inr ⟨(trace_eq_top_iff _ _).mpr ⟨ν, List.prefix_refl _, ht⟩,
        fun h => not_hasLabel_of_label hu (by decide) hb ((trace_eq_top_iff _ _).mp h)⟩
  · rintro ⟨ν, h⟩ hle
    have hm := trace_mono hle ν
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy] at hm; exact hx ((Tree.le_bot_iff _).mp hm)
    · rw [hx] at hm; exact hy ((Tree.top_le_iff _).mp hm)
end DeciSigma1.Semantics.Tree

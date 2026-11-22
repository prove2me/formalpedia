-- Prove2me | solution 1 for DeciSigma1.Arithmetic.simplePath_le_pow_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:55.636266+00:00
-- url     : https://prove2.me/submissions/9553d096-ead8-4ed4-86f6-7241e14ea763

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Theorems.Thm_DeciSigma1_Arithmetic_isChain_and
public import Theorems.Thm_DeciSigma1_Arithmetic_simplePath_le_pow_local
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
namespace DeciSigma1.Arithmetic
theorem _root_.solution {γ : Type*} (f : β → List γ) (H : ℕ) (p : List β)
    (hnd : p.Nodup) (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hH : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ H) :
    p.length ≤ 2 ^ H - 1 := by
  classical
  -- strict prefix, ties broken by the position in the path
  let r : β → β → Prop := fun x y =>
    (f x <+: f y ∧ f x ≠ f y) ∨ (f x = f y ∧ p.idxOf x < p.idxOf y)
  have : IsStrictOrder β r :=
    { irrefl := fun a h => by
        rcases h with ⟨_, h⟩ | ⟨_, h⟩
        · exact h rfl
        · exact lt_irrefl _ h
      trans := fun a b c hab hbc => by
        rcases hab with ⟨hab, hne⟩ | ⟨heq, hlt⟩ <;> rcases hbc with ⟨hbc, hne'⟩ | ⟨heq', hlt'⟩
        · refine Or.inl ⟨hab.trans hbc, fun h => hne ?_⟩
          rw [← h] at hbc
          exact hab.eq_of_length (le_antisymm hab.length_le hbc.length_le)
        · exact Or.inl ⟨heq' ▸ hab, heq' ▸ hne⟩
        · exact Or.inl ⟨heq ▸ hbc, heq ▸ hne'⟩
        · exact Or.inr ⟨heq.trans heq', hlt.trans hlt'⟩ }
  have hkey : ∀ x y, r x y → f x <+: f y := by
    intro x y h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact h ▸ List.prefix_refl _
  have hcomp : ∀ x ∈ p, ∀ y ∈ p, x ≠ y → (f x <+: f y ∨ f y <+: f x) → r x y ∨ r y x := by
    intro x hx y _ hxy h
    by_cases he : f x = f y
    · have hi : p.idxOf x ≠ p.idxOf y := fun hi => hxy ((List.idxOf_inj hx).mp hi)
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · exact Or.inl (Or.inr ⟨he, hi⟩)
      · exact Or.inr (Or.inr ⟨he.symm, hi⟩)
    · rcases h with h | h
      · exact Or.inl (Or.inl ⟨h, he⟩)
      · exact Or.inr (Or.inl ⟨h, Ne.symm he⟩)
  have hne_ch : p.IsChain (fun x y => x ≠ y) := hnd.isChain
  refine simplePath_le_pow_local r H p hnd ?_ ?_ ?_
  · refine (isChain_and hne_ch hp).imp_of_mem_imp ?_
    intro x y hx hy ⟨hxy, h⟩
    exact hcomp x hx y hy hxy h
  · intro x hx y hy z hz hyx hzx
    by_cases hyz : y = z
    · exact Or.inl hyz
    · right
      have h1 := hkey y x hyx
      have h2 := hkey z x hzx
      have hyz' : f y <+: f z ∨ f z <+: f y := by
        rcases le_total (f y).length (f z).length with h | h
        · exact Or.inl (List.prefix_of_prefix_length_le h1 h2 h)
        · exact Or.inr (List.prefix_of_prefix_length_le h2 h1 h)
      exact hcomp y hy z hz hyz hyz'
  · intro c hc hch
    refine hH c hc ?_
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; exact Or.inl (List.prefix_refl _)
    · rcases hch hx hy hxy with h | h
      · exact Or.inl (hkey x y h)
      · exact Or.inr (hkey y x h)
end DeciSigma1.Arithmetic

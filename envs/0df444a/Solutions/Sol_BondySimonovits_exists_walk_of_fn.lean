-- Prove2me | solution 1 for BondySimonovits.exists_walk_of_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:48.570815+00:00
-- url     : https://prove2.me/submissions/d902328e-b6b3-4db4-991e-bb455ef61e4f

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}
namespace BondySimonovits
theorem _root_.solution (K : SimpleGraph V) (c : ℕ → V) :
    ∀ n : ℕ, (∀ t < n, K.Adj (c t) (c (t + 1))) → ∀ u v, c 0 = u → c n = v →
      ∃ p : K.Walk u v, p.support = (List.range (n + 1)).map c ∧ p.length = n := by
  intro n
  induction n with
  | zero => intro _ u v hu hv; subst hu hv; exact ⟨Walk.nil, by simp, rfl⟩
  | succ n ih =>
    intro h u v hu hv
    subst hu hv
    obtain ⟨p, hp, hl⟩ := ih (fun t ht => h t (by omega)) _ _ rfl rfl
    refine ⟨p.concat (h n (by omega)), ?_, ?_⟩
    · rw [Walk.support_concat, hp, List.range_succ (n := n + 1), List.map_append]
      simp
    · simp [hl]
end BondySimonovits

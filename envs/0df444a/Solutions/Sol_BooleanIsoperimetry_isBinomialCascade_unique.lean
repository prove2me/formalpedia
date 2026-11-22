-- Prove2me | solution 1 for BooleanIsoperimetry.isBinomialCascade_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:06.394138+00:00
-- url     : https://prove2.me/submissions/a1f4961a-7838-42a5-a276-ead49000b0e8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {m k r t r' t' : ℕ}
    (h : IsBinomialCascade m k r t) (h' : IsBinomialCascade m k r' t') :
    r = r' ∧ t = t' := by
  obtain ⟨hr, ht, hk, hdisj⟩ := h
  obtain ⟨hr', ht', hk', hdisj'⟩ := h'
  -- The strict case `a < b` for two valid cascade pairs of the same `k` is impossible.
  have key : ∀ a b ta tb, a < b → b ≤ m + 1 → ta ≤ Nat.choose m a →
      (ta < Nat.choose m a ∨ a = m + 1) →
      binomPrefix m a + ta = binomPrefix m b + tb → False := by
    intro a b ta tb hab hbm hta hdisj_a hsum
    have h1 : binomPrefix m (a + 1) ≤ binomPrefix m b :=
      binomPrefix_mono m (Nat.succ_le_of_lt hab)
    rw [binomPrefix_succ] at h1
    rcases hdisj_a with hlt | heq
    · omega
    · omega
  have hrr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · exact (key r r' t t' hlt hr' ht hdisj (hk.symm.trans hk')).elim
    · exact heq
    · exact (key r' r t' t hgt hr ht' hdisj' (hk'.symm.trans hk)).elim
  subst hrr
  exact ⟨rfl, by omega⟩
end BooleanIsoperimetry

-- Prove2me | solution 2 for AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:40:33.941432+00:00
-- url     : https://prove2.me/submissions/08e3ada8-f679-41d2-9b82-e7c1d918007f

import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- Any finite nonnegative time set has a monotone zero-based enumeration grid. -/
theorem solution (J : Finset ℝ≥0) :
    ∃ (n : ℕ) (t : ℕ → ℝ≥0) (e : J → Fin n),
      Monotone t ∧ t 0 = 0 ∧
      ∀ j : J, t ((e j).val + 1) = (j : ℝ≥0) := by
  classical
  let K : Finset ℝ≥0 := insert 0 J
  have hn : 0 < K.card := Finset.card_pos.mpr
    ⟨0, Finset.mem_insert_self 0 J⟩
  let f : Fin K.card ↪o ℝ≥0 := K.orderEmbOfFin rfl
  let idx : ℕ → Fin K.card := fun k =>
    ⟨min k (K.card - 1), Nat.lt_of_le_of_lt
      (Nat.min_le_right k (K.card - 1))
      (Nat.sub_lt hn (by omega))⟩
  have hidx : Monotone idx := by
    intro a b hab
    change min a (K.card - 1) ≤ min b (K.card - 1)
    omega
  have hidx_eval (i : Fin K.card) : idx i.val = i := by
    apply Fin.ext
    change min i.val (K.card - 1) = i.val
    have hi : i.val ≤ K.card - 1 := by omega
    exact Nat.min_eq_left hi
  let t : ℕ → ℝ≥0 := fun k =>
    if k = 0 then 0 else f (idx (k - 1))
  have ht0 : t 0 = 0 := by simp [t]
  have ht : Monotone t := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      simpa only [ht0] using (show (0 : ℝ≥0) ≤ t b from zero_le)
    · have hb : b ≠ 0 := by omega
      have h := f.monotone (hidx (Nat.sub_le_sub_right hab 1))
      simpa only [t, if_neg ha, if_neg hb] using h
  have ht_step (i : Fin K.card) : t (i.val + 1) = f i := by
    have hh : i.val + 1 ≠ 0 := by omega
    calc
      t (i.val + 1) = f (idx i.val) := by simp [t, hh]
      _ = f i := by rw [hidx_eval]
  have hRange : ∀ j : J, ∃ i : Fin K.card, f i = (j : ℝ≥0) := by
    intro j
    have hj : (j : ℝ≥0) ∈ K :=
      Finset.mem_insert_of_mem j.property
    have hmem : (j : ℝ≥0) ∈ Set.range f := by
      rw [show Set.range f = (K : Set ℝ≥0) from
        Finset.range_orderEmbOfFin K rfl]
      exact hj
    exact Set.mem_range.mp hmem
  let e : J → Fin K.card := fun j => Classical.choose (hRange j)
  refine ⟨K.card, t, e, ht, ht0, ?_⟩
  intro j
  rw [ht_step]
  exact Classical.choose_spec (hRange j)

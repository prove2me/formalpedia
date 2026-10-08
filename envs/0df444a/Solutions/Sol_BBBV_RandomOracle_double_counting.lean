-- Prove2me | solution 1 for BBBV.RandomOracle.double_counting
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:43:12.526001+00:00
-- url     : https://prove2.me/submissions/8f3b2820-163a-45b9-9d23-323dc0ff38fe

import Mathlib
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

open Classical in
theorem double_counting {n : ℕ} (hn : 1 ≤ n) (Good : (Str n → Str n) → Prop)
    (h : ∀ A, NoInverse A → Good A →
      2 ^ (n - 1) ≤ (Finset.univ.filter fun y => ¬ Good (Function.update A y (ones n))).card) :
    (Finset.univ.filter fun A => NoInverse A ∧ Good A).card ≤
      2 * (Finset.univ.filter fun B => UniqueInverse B ∧ ¬ Good B).card := by
  classical
  let s := Finset.univ.filter (fun A : Str n → Str n => NoInverse A ∧ Good A)
  let t := Finset.univ.filter (fun B : Str n → Str n => UniqueInverse B ∧ ¬ Good B)
  let r : (Str n → Str n) → (Str n → Str n) → Prop :=
    fun A B => ∃ y, Function.update A y (ones n) = B
  have hu (A : Str n → Str n) (hA : NoInverse A) (y : Str n) :
      UniqueInverse (Function.update A y (ones n)) := by
    refine ⟨y, by simp, ?_⟩
    intro z hz
    by_contra hzy
    have hh : A z = ones n := by
      simpa [Function.update_of_ne hzy] using hz
    exact hA z hh
  have hleft : ∀ A ∈ s, 2 ^ (n - 1) ≤ (t.bipartiteAbove r A).card := by
    intro A hAs
    have hA := (Finset.mem_filter.mp hAs).2
    let u := Finset.univ.filter (fun y => ¬ Good (Function.update A y (ones n)))
    have hinj : Set.InjOn (fun y => Function.update A y (ones n)) u := by
      intro y hy z hz heq
      change Function.update A y (ones n) = Function.update A z (ones n) at heq
      have hh : Function.update A z (ones n) y = ones n := by rw [← heq]; simp
      exact (hu A hA.1 z).unique hh (by simp)
    have hmap : u.image (fun y => Function.update A y (ones n)) ⊆ t.bipartiteAbove r A := by
      intro B hB
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hB
      apply (Finset.mem_bipartiteAbove r).mpr
      refine ⟨?_, ⟨y, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu A hA.1 y,
        (Finset.mem_filter.mp hy).2⟩
    calc
      2 ^ (n - 1) ≤ u.card := h A hA.1 hA.2
      _ = (u.image (fun y => Function.update A y (ones n))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card hmap
  have hright : ∀ B ∈ t, (s.bipartiteBelow r B).card ≤ 2 ^ n := by
    intro B hBt
    obtain ⟨y, hy, huniq⟩ := (Finset.mem_filter.mp hBt).2.1
    have hinj : Set.InjOn (fun A : Str n → Str n => A y) (s.bipartiteBelow r B) := by
      intro A hA C hC heq
      obtain ⟨hAs, z, hz⟩ := (Finset.mem_bipartiteBelow r).mp hA
      obtain ⟨hCs, w, hw⟩ := (Finset.mem_bipartiteBelow r).mp hC
      have hzy : z = y := huniq z (by rw [← hz]; simp)
      have hwy : w = y := huniq w (by rw [← hw]; simp)
      subst z
      subst w
      funext v
      by_cases hv : v = y
      · subst v; exact heq
      · have ha : A v = B v := by rw [← hz]; simp [Function.update_of_ne hv]
        have hc : C v = B v := by rw [← hw]; simp [Function.update_of_ne hv]
        exact ha.trans hc.symm
    calc
      (s.bipartiteBelow r B).card =
          ((s.bipartiteBelow r B).image (fun A => A y)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card (Str n) := Finset.card_le_univ _
      _ = 2 ^ n := by simp [Str, Fintype.card_fun]
  have hh := Finset.card_mul_le_card_mul r hleft hright
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  rw [hp] at hh
  have hpos : 0 < 2 ^ (n - 1) := by positivity
  change s.card ≤ 2 * t.card
  apply (Nat.mul_le_mul_right_iff hpos).mp
  nlinarith [hh]


end BBBV.RandomOracle

open BBBV.RandomOracle

open Classical in
theorem solution {n : ℕ} (hn : 1 ≤ n) (Good : (Str n → Str n) → Prop)
    (h : ∀ A, NoInverse A → Good A →
      2 ^ (n - 1) ≤ (Finset.univ.filter fun y => ¬ Good (Function.update A y (ones n))).card) :
    (Finset.univ.filter fun A => NoInverse A ∧ Good A).card ≤
      2 * (Finset.univ.filter fun B => UniqueInverse B ∧ ¬ Good B).card := BBBV.RandomOracle.double_counting hn Good h


#print axioms solution

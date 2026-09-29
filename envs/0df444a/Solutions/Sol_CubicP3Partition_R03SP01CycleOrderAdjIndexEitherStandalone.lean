-- Prove2me | solution 1 for CubicP3Partition.R03SP01CycleOrderAdjIndexEitherStandalone
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:07.602635+00:00
-- url     : https://prove2.me/submissions/4a21d225-df7f-4f76-8604-6c3cfaf65d60

import Mathlib

namespace CubicP3Partition

universe u


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {X : Type u}
    (R : SimpleGraph X)
    (hcycles : R.IsCycles)
    (n : Nat) (hn : 3 ≤ n)
    (e : Fin n → X)
    (hinj : Function.Injective e)
    (cycle : ∀ i : Fin n,
      R.Adj (e i) (e ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩))
    (i j : Fin n) (hadj : R.Adj (e i) (e j)) :
    j = ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ ∨
      i = ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
  let next : Fin n → Fin n := fun t =>
    ⟨(t.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  let prev : Fin n → Fin n := fun t =>
    ⟨if t.val = 0 then n - 1 else t.val - 1, by split <;> omega⟩
  have hnext (t : Fin n) : R.Adj (e t) (e (next t)) := by
    exact cycle t
  have hprevnext (t : Fin n) : next (prev t) = t := by
    apply Fin.ext
    dsimp [next, prev]
    by_cases ht : t.val = 0
    · simp only [ht, ↓reduceIte]
      have hEq : n - 1 + 1 = n := by omega
      rw [hEq, Nat.mod_self]
    · simp only [ht, ↓reduceIte]
      have hEq : t.val - 1 + 1 = t.val := by omega
      rw [hEq, Nat.mod_eq_of_lt t.isLt]
  have hprev_adj (t : Fin n) : R.Adj (e t) (e (prev t)) := by
    have h := hnext (prev t)
    rw [hprevnext t] at h
    exact h.symm
  have hprev_ne_next (t : Fin n) : prev t ≠ next t := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [prev, next] at hv
    by_cases ht : t.val = 0
    · simp only [ht, ↓reduceIte] at hv
      have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod] at hv
      omega
    · simp only [ht, ↓reduceIte] at hv
      by_cases hlast : t.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlast] at hv
        omega
      · have htlast : t.val = n - 1 := by omega
        rw [htlast] at hv
        have hmod : (n - 1 + 1) % n = 0 := by
          rw [show n - 1 + 1 = n by omega, Nat.mod_self]
        rw [hmod] at hv
        omega
  by_cases hij : j = next i
  · exact Or.inl hij
  · right
    have hne : e (next i) ≠ e j := by
      intro h
      apply hij
      apply hinj
      exact h.symm
    have hu := hcycles.existsUnique_ne_adj (hnext i)
    have huniq := hu.unique
      ⟨hne, hadj⟩
      ⟨by
        intro h
        apply hprev_ne_next i
        apply hinj
        exact h.symm, hprev_adj i⟩
    have hej : e j = e (prev i) := huniq
    have hjprev : j = prev i := hinj hej
    have hnextj : next j = i := by
      rw [hjprev]
      exact hprevnext i
    exact hnextj.symm


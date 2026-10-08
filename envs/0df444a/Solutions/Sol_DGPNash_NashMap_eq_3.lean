-- Prove2me | solution 1 for DGPNash.NashMap.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:52:35.326071+00:00
-- url     : https://prove2.me/submissions/447f89d3-1e18-4d2a-a738-ee2ac03e4520

import Mathlib
import Definitions.Def_DGPNash_NashMap_nashMap

namespace FC7480BA

open Finset

lemma sum_profileProb_eq_one {r n : ℕ} (y : Fin r → Fin n → ℝ)
    (hy : ∀ i, ∑ a, y i a = 1) :
    ∑ s : Fin r → Fin n, AGT.profileProb y s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum (fun i a => y i a)]
  simp [hy]

lemma profileProb_nonneg {r n : ℕ} (y : Fin r → Fin n → ℝ)
    (hy : ∀ i a, 0 ≤ y i a) (s : Fin r → Fin n) :
    0 ≤ AGT.profileProb y s := by
  unfold AGT.profileProb
  exact Finset.prod_nonneg (fun i _ => hy i (s i))

lemma le_maxPayoff {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r)
    (s : Fin r → Fin n) : u p s ≤ DGPNash.NashMap.maxPayoff u := by
  unfold DGPNash.NashMap.maxPayoff
  exact le_csSup (Set.finite_range _).bddAbove ⟨(p, s), rfl⟩

lemma expectedPayoff_le {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (p : Fin r)
    (y : Fin r → Fin n → ℝ) (hy0 : ∀ i a, 0 ≤ y i a) (hy1 : ∀ i, ∑ a, y i a = 1) :
    AGT.expectedPayoff u y p ≤ DGPNash.NashMap.maxPayoff u := by
  unfold AGT.expectedPayoff
  calc ∑ s, AGT.profileProb y s * u p s
      ≤ ∑ s, AGT.profileProb y s * DGPNash.NashMap.maxPayoff u := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (le_maxPayoff u p s) (profileProb_nonneg y hy0 s)
    _ = DGPNash.NashMap.maxPayoff u := by
        rw [← Finset.sum_mul, sum_profileProb_eq_one y hy1, one_mul]

lemma expectedPayoff_nonneg {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ)
    (hu : ∀ p s, 0 ≤ u p s) (p : Fin r)
    (y : Fin r → Fin n → ℝ) (hy0 : ∀ i a, 0 ≤ y i a) :
    0 ≤ AGT.expectedPayoff u y p := by
  unfold AGT.expectedPayoff
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (profileProb_nonneg y hy0 s) (hu p s))

lemma gain_le {r n : ℕ} (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x) (p : Fin r) (j : Fin n) :
    DGPNash.NashMap.gain u x p j ≤ DGPNash.NashMap.maxPayoff u := by
  have hx0 : ∀ i a, 0 ≤ x i a := fun i a => (hx i).1 a
  have hx1 : ∀ i, ∑ a, x i a = 1 := fun i => (hx i).2
  set y := Function.update x p (fun k => if k = j then (1:ℝ) else 0) with hydef
  have hy0 : ∀ i a, 0 ≤ y i a := by
    intro i a
    by_cases h : i = p
    · subst h; simp only [hydef, Function.update_self]; split_ifs <;> norm_num
    · simp only [hydef, Function.update_of_ne h]; exact hx0 i a
  have hy1 : ∀ i, ∑ a, y i a = 1 := by
    intro i
    by_cases h : i = p
    · subst h; simp [hydef, Function.update_self]
    · simp only [hydef, Function.update_of_ne h]; exact hx1 i
  have h1 : DGPNash.NashMap.purePayoff u x p j ≤ DGPNash.NashMap.maxPayoff u :=
    expectedPayoff_le u p y hy0 hy1
  have h2 := expectedPayoff_nonneg u hu p x hx0
  have h3 : 0 ≤ DGPNash.NashMap.maxPayoff u := le_trans (hu p (fun _ => j)) (le_maxPayoff u p _)
  unfold DGPNash.NashMap.gain
  exact max_le h3 (by linarith)

end FC7480BA

open Finset in
open DGPNash.NashMap in
theorem solution {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x : Fin r → Fin n → ℝ) (hx : AGT.IsMixedProfile x)
    (ε' : ℝ) (hε' : 0 ≤ ε')
    (hclose : ∀ p j, |nashMap u x p j - x p j| ≤ ε') :
    ∀ p j, x p j * (∑ i : Fin n, gain u x p i) ≤
      gain u x p j + ε' * (1 + (n : ℝ) * maxPayoff u) := by
  intro p j
  have hg0 : ∀ i, 0 ≤ gain u x p i := fun i => le_max_left _ _
  set S := ∑ i : Fin n, gain u x p i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hg0 i)
  have hSle : S ≤ (n : ℝ) * maxPayoff u := by
    calc S ≤ ∑ _i : Fin n, maxPayoff u :=
          Finset.sum_le_sum (fun i _ => FC7480BA.gain_le u hu x hx p i)
      _ = (n : ℝ) * maxPayoff u := by simp
  have hpos : 0 < 1 + S := by linarith
  have h := (abs_le.mp (hclose p j)).1
  have hf : nashMap u x p j = (x p j + gain u x p j) / (1 + S) := rfl
  rw [hf] at h
  have h' : (x p j - ε') * (1 + S) ≤ x p j + gain u x p j := by
    have : x p j - ε' ≤ (x p j + gain u x p j) / (1 + S) := by linarith
    rwa [le_div_iff₀ hpos] at this
  have h4 : ε' * S ≤ ε' * ((n : ℝ) * maxPayoff u) := mul_le_mul_of_nonneg_left hSle hε'
  nlinarith

-- Prove2me | solution 1 for Freiman.padded_copies_centers
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:17:10.39372+00:00
-- url     : https://prove2.me/submissions/6321cc50-be5f-47d7-a740-c48a8e62bb44

import Definitions.Def_Freiman_paddedCopies
import Theorems.Thm_Freiman_localValue_window_bound
import Theorems.Thm_Freiman_localValue_shift
import Theorems.Thm_Freiman_cylinder_bound_tendsto

open Freiman

set_option autoImplicit false

private theorem start_succ (j : ℕ) :
    paddedStart (j + 1) = paddedStart j + 4 * j + 1 := by
  cases j with
  | zero => norm_num [paddedStart]
  | succ j =>
    have h₁ : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    have h₂ : 2 * (j + 1 + 1) - 1 = 2 * j + 3 := by omega
    simp only [paddedStart, h₁, h₂]
    ring

private theorem copy_offset (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d) (j : ℕ) (u : ℤ)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ ((4 * j : ℕ) : ℤ)) :
    b ((paddedStart j : ℤ) + u) = a j (u - ((2 * j : ℕ) : ℤ)) := by
  have hu : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu₀
  have hn : u.toNat ≤ 4 * j := by omega
  simpa only [Nat.cast_add, hu] using hcopy.2 j u.toNat hn

private theorem value_comparison (a b : ℤ → ℕ+) (i j : ℤ) (R : ℕ)
    (h : ∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → a (i + k) = b (j + k)) :
    |localValue a i - localValue b j| ≤ 2 / ((Nat.fib (R + 1) : ℝ) ^ 2) := by
  have hw := localValue_window_bound (fun k : ℤ => a (i + k))
    (fun k : ℤ => b (j + k)) 0 R (by
      intro k hk₀ hk₁
      exact h k (by simpa using hk₀) (by simpa using hk₁))
  simpa only [localValue_shift, add_zero] using hw

theorem solution (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ)
    (hcopy : PaddedCopies a b d)
    (hcentral : Filter.Tendsto (fun j : ℕ => localValue (a j) 0) Filter.atTop (nhds t)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Filter.Tendsto (fun j : ℕ => localValue b (p j : ℤ)) Filter.atTop (nhds t) := by
  let p : ℕ → ℕ := fun j => paddedStart j + 2 * j
  have hp : StrictMono p := by
    apply strictMono_nat_of_lt_succ
    intro j
    change paddedStart j + 2 * j < paddedStart (j + 1) + 2 * (j + 1)
    rw [start_succ]
    omega
  have hwindow (j : ℕ) : ∀ k : ℤ, -(j : ℤ) ≤ k → k ≤ (j : ℤ) →
      b ((p j : ℤ) + k) = a j (0 + k) := by
    intro k hk₀ hk₁
    have hu₀ : (0 : ℤ) ≤ ((2 * j : ℕ) : ℤ) + k := by omega
    have hu₁ : ((2 * j : ℕ) : ℤ) + k ≤ ((4 * j : ℕ) : ℤ) := by omega
    have hc := copy_offset a b d hcopy j (((2 * j : ℕ) : ℤ) + k) hu₀ hu₁
    have he : (((2 * j : ℕ) : ℤ) + k) - ((2 * j : ℕ) : ℤ) = k := by omega
    simpa only [p, Nat.cast_add, add_assoc, he, zero_add] using hc
  have hbound (j : ℕ) : |localValue b (p j : ℤ) - localValue (a j) 0| ≤
      2 / ((Nat.fib (j + 1) : ℝ) ^ 2) :=
    value_comparison b (a j) (p j : ℤ) 0 j (hwindow j)
  refine ⟨p, hp, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 cylinder_bound_tendsto (ε / 2) hhalf
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hcentral (ε / 2) hhalf
  refine ⟨max N₁ N₂, ?_⟩
  intro j hj
  have h₁ : 2 / ((Nat.fib (j + 1) : ℝ) ^ 2) < ε / 2 := by
    apply (le_abs_self _).trans_lt
    simpa only [Real.dist_eq, sub_zero] using hN₁ j ((le_max_left _ _).trans hj)
  have h₂ : |localValue (a j) 0 - t| < ε / 2 := by
    simpa only [Real.dist_eq] using hN₂ j ((le_max_right _ _).trans hj)
  rw [Real.dist_eq]
  calc
    |localValue b (p j : ℤ) - t| ≤
        |localValue b (p j : ℤ) - localValue (a j) 0| + |localValue (a j) 0 - t| :=
      abs_sub_le _ _ _
    _ < ε := by linarith [hbound j]

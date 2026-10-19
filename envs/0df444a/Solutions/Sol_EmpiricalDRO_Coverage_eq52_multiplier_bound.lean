-- Prove2me | solution 1 for EmpiricalDRO.Coverage.eq52_multiplier_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:29:30.541981+00:00
-- url     : https://prove2.me/submissions/b39f7294-c111-46f0-9381-f8889ca7bab0

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ lam : ℝ)
    (hpos : ∀ i, 0 < 1 + lam * (z i - μ))
    (h50 : ∑ i, (1 / (n : ℝ)) * ((z i - μ) / (1 + lam * (z i - μ))) = 0) :
    |lam| * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2 -
        |(1 / (n : ℝ)) * ∑ i, (z i - μ)| * ⨆ i, |z i - μ|) ≤
      |(1 / (n : ℝ)) * ∑ i, (z i - μ)| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set M : ℝ := ⨆ i, |z i - μ| with hM
  have hle : ∀ i, |z i - μ| ≤ M := fun i =>
    le_ciSup (Set.finite_range (fun j => |z j - μ|)).bddAbove i
  set S : ℝ := ∑ i, (z i - μ) with hS
  set Q : ℝ := ∑ i, (z i - μ) ^ 2 with hQ
  set c : ℝ := 1 + |lam| * M with hc
  have hM0 : 0 ≤ M := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact le_trans (abs_nonneg _) (hle ⟨0, hn⟩)
  have hcpos : 0 < c := by positivity
  have hai : ∀ i, 1 + lam * (z i - μ) ≤ c := by
    intro i
    have h1 : lam * (z i - μ) ≤ |lam| * |z i - μ| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |lam| * |z i - μ| ≤ |lam| * M :=
      mul_le_mul_of_nonneg_left (hle i) (abs_nonneg _)
    rw [hc]; linarith
  -- sum of h/a is zero
  have h50' : ∑ i, (z i - μ) / (1 + lam * (z i - μ)) = 0 := by
    rw [← Finset.mul_sum] at h50
    rcases mul_eq_zero.mp h50 with h | h
    · exfalso; simp at h; omega
    · exact h
  have hid : ∀ i, (z i - μ) = (z i - μ) / (1 + lam * (z i - μ))
      + lam * ((z i - μ) ^ 2 / (1 + lam * (z i - μ))) := by
    intro i
    have := (hpos i).ne'
    symm
    rw [← mul_div_assoc, ← add_div, div_eq_iff this]
    ring
  have hSeq : S = lam * ∑ i, (z i - μ) ^ 2 / (1 + lam * (z i - μ)) := by
    rw [hS, Finset.mul_sum]
    calc ∑ i, (z i - μ)
        = ∑ i, ((z i - μ) / (1 + lam * (z i - μ))
          + lam * ((z i - μ) ^ 2 / (1 + lam * (z i - μ)))) :=
          Finset.sum_congr rfl (fun i _ => hid i)
      _ = _ := by rw [Finset.sum_add_distrib, h50', zero_add]
  have hlow : Q / c ≤ ∑ i, (z i - μ) ^ 2 / (1 + lam * (z i - μ)) := by
    rw [hQ, Finset.sum_div]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hpos i) (hai i)
  have habsS : |S| = |lam| * ∑ i, (z i - μ) ^ 2 / (1 + lam * (z i - μ)) := by
    rw [hSeq, abs_mul]
    congr 1
    apply abs_of_nonneg
    exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hpos i).le)
  have key : |lam| * Q ≤ |S| * c := by
    have : |lam| * (Q / c) ≤ |S| := by
      rw [habsS]; exact mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hcpos] at this
    exact this
  have e1 : (1 / (n : ℝ)) * Q = Q / n := by ring
  have e2 : |(1 / (n : ℝ)) * S| = |S| / n := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]; ring
  rw [e1, e2]
  have : |lam| * (Q / n - |S| / n * M) = (|lam| * Q - |lam| * |S| * M) / n := by
    field_simp
  rw [this, div_le_div_iff_of_pos_right hnpos]
  rw [hc] at key
  nlinarith [key]

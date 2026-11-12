-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger166_clipped_discount_chronological_weighted_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:10:13.445316+00:00
-- url     : https://prove2.me/submissions/a78b0165-bcbd-4bc7-b308-218d717fe60f

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
import Theorems.Thm_AvramDividend_Classical_avram_gledger167_clipped_discount_exp_weighted_sum_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger168_clipped_discount_counterterm_sum_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
theorem solution
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (q : ℝ) (W : ℕ → ℝ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∃ k : ℕ, k ≤ m ∧
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * W i) +
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ then q * (Δ : ℝ) * E s * W i else 0) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
      (E ρ - E ((k : ℝ≥0) * Δ) +
        (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k := by
  intro Δ v E
  obtain ⟨k, hk, hstart, hcross, hbefore, hafter⟩ :=
    avram_gledger163_true_uniform_clipped_mesh_first_crossing n m hn ρ hρn hρpos
  have hkm : k ≤ m := by omega
  have hmin (i : ℕ) (hi : v i < ρ) : (i : ℝ≥0) * Δ < ρ := by
    by_contra h
    have hc : ρ ≤ (i : ℝ≥0) * Δ := le_of_not_gt h
    have heq : v i = ρ := min_eq_right hc
    exact (lt_irrefl ρ) (heq ▸ hi)
  have hlo : ∀ i : ℕ, i ≤ k → (i : ℝ≥0) * Δ < ρ := by
    intro i hi
    by_cases hik : i = k
    · exact hmin i (hik ▸ hstart)
    · have hi' : i < k := by omega
      have hv := hmin (i + 1) (hbefore i hi')
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) Δ.property) hv
  have hhi : ∀ i : ℕ, k < i → ρ ≤ (i : ℝ≥0) * Δ := by
    intro i hi
    by_contra h
    have hs : (i : ℝ≥0) * Δ < ρ := lt_of_not_ge h
    have heq : v i = (i : ℝ≥0) * Δ := min_eq_left hs.le
    exact (ne_of_lt hs) (heq.symm.trans (hafter i hi))
  have hfirst :=
    avram_gledger167_clipped_discount_exp_weighted_sum_partition
      n m ρ q W k hkm (by simpa only [Δ] using hlo) (by simpa only [Δ] using hhi)
  have hsecond :=
    avram_gledger168_clipped_discount_counterterm_sum_partition
      n m ρ q W k hkm (by simpa only [Δ] using hlo) (by simpa only [Δ] using hhi)
  refine ⟨k, hkm, ?_⟩
  change
    (∑ i ∈ Finset.range (m + 1), (E (v (i + 1)) - E (v i)) * W i) +
      (∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ < ρ then
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ) * W i else 0) =
      (∑ i ∈ Finset.range k,
        (E (((i + 1 : ℕ) : ℝ≥0) * Δ) - E ((i : ℝ≥0) * Δ) +
          q * (Δ : ℝ) * E ((i : ℝ≥0) * Δ)) * W i) +
      (E ρ - E ((k : ℝ≥0) * Δ) +
        (if k < m then q * (Δ : ℝ) * E ((k : ℝ≥0) * Δ) else 0)) * W k
  rw [hfirst, hsecond]
  simp only [add_mul, Finset.sum_add_distrib]
  by_cases hkm' : k < m
  · simp only [if_pos hkm']; ring
  · simp only [if_neg hkm']; ring

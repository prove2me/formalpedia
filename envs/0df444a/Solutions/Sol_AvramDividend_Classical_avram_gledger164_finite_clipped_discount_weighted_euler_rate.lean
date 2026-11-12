-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger164_finite_clipped_discount_weighted_euler_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:42:44.172174+00:00
-- url     : https://prove2.me/submissions/328ffdb3-62c2-4d85-9c28-2f413be80a61

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
import Theorems.Thm_AvramDividend_Classical_avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
import Theorems.Thm_AvramDividend_Classical_avram_gledger170_clipped_discount_crossing_witness_exact_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger171_discount_last_crossing_conditional_boundary
import Theorems.Thm_AvramDividend_Classical_avram_gledger173_discount_coe_exact_real_partition_normalization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
theorem solution
    (n m : ℕ) (hn : 0 < n) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (q K : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K) (W : ℕ → ℝ)
    (hW : ∀ i : ℕ, i ≤ m →
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) < ρ → |W i| ≤ K) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    |(∑ i ∈ Finset.range (m + 1), (E (v (i + 1)) - E (v i)) * W i) +
       ∑ i ∈ Finset.range m,
         let s : ℝ≥0 := (i : ℝ≥0) * Δ
         if s < ρ then q * (Δ : ℝ) * E s * W i else 0| ≤
      (m : ℝ) * ((q * (Δ : ℝ)) ^ 2 * K) + 2 * q * (Δ : ℝ) * K := by
  intro Δ v E
  by_cases hz : ρ = 0
  · subst ρ
    simp [v]
    positivity
  have hpos : 0 < ρ := pos_iff_ne_zero.mpr hz
  obtain ⟨k, hkm, hactive, hcross, hpart⟩ :=
    avram_gledger170_clipped_discount_crossing_witness_exact_partition
      n m hn ρ hρn hpos q W
  have hδ : 0 ≤ (Δ : ℝ) := NNReal.coe_nonneg Δ
  have hpre (i : ℕ) (hi : i < k) : (i : ℝ≥0) * Δ < ρ := by
    apply lt_of_le_of_lt _ hactive
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt hi) Δ.property
  have hweights : ∀ i ∈ Finset.range k, |W i| ≤ K := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    exact hW i ((Nat.le_of_lt hik).trans hkm) (by simpa only [Δ] using hpre i hik)
  have hkW : |W k| ≤ K := hW k hkm (by simpa only [Δ] using hactive)
  let s : ℕ → ℝ := fun i => (((i : ℝ≥0) * Δ : ℝ≥0) : ℝ)
  let t : ℝ := (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ)
  let r : ℝ := (ρ : ℝ) - t
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by
    exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr hactive.le)
  have hstep (i : ℕ) : (((i + 1 : ℕ) : ℝ≥0) * Δ : ℝ) =
      s i + (Δ : ℝ) := by
    simp [s, Nat.cast_add, add_mul, NNReal.coe_mul, NNReal.coe_add]
  have hrδ : r ≤ (Δ : ℝ) := by
    have he : (ρ : ℝ) ≤ (((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ) :=
      NNReal.coe_le_coe.mpr hcross
    have hs : (((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ) =
        (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ) + (Δ : ℝ) := hstep k
    change (ρ : ℝ) - (((k : ℝ≥0) * Δ : ℝ≥0) : ℝ) ≤ (Δ : ℝ)
    linarith
  have hcell : ∀ i ∈ Finset.range k,
      |Real.exp (-(q * (s i + (Δ : ℝ)))) -
        Real.exp (-(q * s i)) + q * (Δ : ℝ) *
          Real.exp (-(q * s i))| ≤ (q * (Δ : ℝ)) ^ 2 := by
    intro i hi
    exact avram_gledger169_discount_exponential_Euler_quadratic_cell_all_scales
      q (s i) (Δ : ℝ) hq (by dsimp [s]; positivity) hδ
  have hsum := avram_gledger146_finite_discount_Euler_cell_absolute_aggregation
    k q (Δ : ℝ) K s W hK hweights hcell
  have hbound := avram_gledger171_discount_last_crossing_conditional_boundary
    q t r (Δ : ℝ) (W k) K hq ht hr hrδ hK hkW (k < m)
  have hnorm := avram_gledger173_discount_coe_exact_real_partition_normalization
    m k ρ Δ q W
  calc
    |(∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * W i) +
       ∑ i ∈ Finset.range m,
         let s : ℝ≥0 := (i : ℝ≥0) * Δ
         if s < ρ then q * (Δ : ℝ) * E s * W i else 0| =
      |(∑ i ∈ Finset.range k,
         (Real.exp (-(q * (s i + (Δ : ℝ)))) -
          Real.exp (-(q * s i)) + q * (Δ : ℝ) *
            Real.exp (-(q * s i))) * W i) +
       (Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
          (if k < m then q * (Δ : ℝ) *
             Real.exp (-(q * t)) else 0)) * W k| := by
            rw [hpart]
            exact congrArg abs hnorm
    _ ≤ |∑ i ∈ Finset.range k,
         (Real.exp (-(q * (s i + (Δ : ℝ)))) -
          Real.exp (-(q * s i)) + q * (Δ : ℝ) *
            Real.exp (-(q * s i))) * W i| +
        |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
          (if k < m then q * (Δ : ℝ) *
             Real.exp (-(q * t)) else 0)) * W k| := abs_add_le _ _
    _ ≤ (k : ℝ) * ((q * (Δ : ℝ)) ^ 2 * K) +
        2 * q * (Δ : ℝ) * K := add_le_add hsum hbound
    _ ≤ (m : ℝ) * ((q * (Δ : ℝ)) ^ 2 * K) +
        2 * q * (Δ : ℝ) * K := by
          gcongr

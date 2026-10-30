-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_partition_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:48:18.987218+00:00
-- url     : https://prove2.me/submissions/a7656fea-ce8c-4737-806c-fe09645f6f68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω|) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) +
        (D (u n) ω - D (u 0) ω) := by
  filter_upwards [bv_actual_path_partition_variation_bound_ws01b X hX hBV] with ω hω
  intro u hu n
  have hmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
  have hpoint (i : ℕ) :
      |riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω| ≤
      |X.X (u (i + 1)) ω - X.X (u i) ω| +
        (D (u (i + 1)) ω - D (u i) ω) := by
    have hDnonneg : 0 ≤ D (u (i + 1)) ω - D (u i) ω :=
      sub_nonneg.mpr (hmono (hu (Nat.le_add_right i 1)))
    have heq : riskProcess X x D (u (i + 1)) ω - riskProcess X x D (u i) ω =
        (X.X (u (i + 1)) ω - X.X (u i) ω) -
          (D (u (i + 1)) ω - D (u i) ω) := by
      simp only [riskProcess]
      ring
    rw [heq]
    calc
      _ ≤ |X.X (u (i + 1)) ω - X.X (u i) ω| +
          |D (u (i + 1)) ω - D (u i) ω| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (X.X (u (i + 1)) ω - X.X (u i) ω)
                (0 : ℝ) (D (u (i + 1)) ω - D (u i) ω))
      _ = _ := by rw [abs_of_nonneg hDnonneg]
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hpoint i)
  have htel :
      (∑ i ∈ Finset.range n, (D (u (i + 1)) ω - D (u i) ω)) =
        D (u n) ω - D (u 0) ω := by
    simpa only using (Finset.sum_range_sub (fun j => D (u j) ω) n)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (|X.X (u (i + 1)) ω - X.X (u i) ω| +
          (D (u (i + 1)) ω - D (u i) ω)) := hsum
    _ = (∑ i ∈ Finset.range n, |X.X (u (i + 1)) ω - X.X (u i) ω|) +
          (D (u n) ω - D (u 0) ω) := by rw [Finset.sum_add_distrib, htel]
    _ ≤ _ := by
      have hbound := hω u hu n
      linarith only [hbound]

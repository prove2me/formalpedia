-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_partition_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T18:31:07.006465+00:00
-- url     : https://prove2.me/submissions/32125edf-582c-4263-b088-54378e4589c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Full source BV Lévy variation bound for the genuine right-limit
    post-payment reserve, with all time-zero and later dividend jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω)|) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) +
        (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by
  filter_upwards [bv_actual_path_partition_variation_bound_ws01b X hX hBV] with ω hω
  intro u hu n
  have hmono : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hpoint (i : ℕ) :
      |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω)| ≤
      |X.X (u (i + 1)) ω - X.X (u i) ω| +
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    have hDnonneg : 0 ≤ rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω :=
      sub_nonneg.mpr (hmono (hu (Nat.le_add_right i 1)))
    have heq :
        (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω) =
        (X.X (u (i + 1)) ω - X.X (u i) ω) -
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by ring
    rw [heq]
    calc
      _ ≤ |X.X (u (i + 1)) ω - X.X (u i) ω| +
          |rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (X.X (u (i + 1)) ω - X.X (u i) ω)
                (0 : ℝ) (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))
      _ = _ := by rw [abs_of_nonneg hDnonneg]
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hpoint i)
  have htel :
      (∑ i ∈ Finset.range n,
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) =
        rightLimit D (u n) ω - rightLimit D (u 0) ω := by
    simpa only using (Finset.sum_range_sub (fun j => rightLimit D (u j) ω) n)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (|X.X (u (i + 1)) ω - X.X (u i) ω| +
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) := hsum
    _ = (∑ i ∈ Finset.range n,
          |X.X (u (i + 1)) ω - X.X (u i) ω|) +
          (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by
        rw [Finset.sum_add_distrib, htel]
    _ ≤ _ := by
      have hbound := hω u hu n
      linarith only [hbound]

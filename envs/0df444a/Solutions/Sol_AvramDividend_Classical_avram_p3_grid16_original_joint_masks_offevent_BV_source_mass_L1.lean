-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid16_original_joint_masks_offevent_BV_source_mass_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:35:16.587982+00:00
-- url     : https://prove2.me/submissions/c30868e4-bd52-4764-8a74-f86b7a4e8097

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Joint original cofinal localisation and its fixed-clock source-mass tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (coeff : ℕ → Ω → ℕ → ℝ)
    (hcoeff : ∀ n i, Measurable (fun ω => coeff n ω i))
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (L : ℝ) (hL : 0 ≤ L) :
    ∃ κ K : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, n ≤ κ n) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n ω, ω ∈ s n →
        (∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))) ∧
        (∀ i ∈ Finset.range (n + 1),
          abs (coeff n ω i) ≤ (K n : ℝ))) ∧
      (∀ n, Integrable
        (fun ω => if ω ∈ s n then 0 else
          L * (|X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto
        (fun n => ∫ ω, if ω ∈ s n then 0 else
          L * (|X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by
  classical
  obtain ⟨κ, K, s, hκ, hsm, he, hmask⟩ :=
    avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
      X x D hD C a b hExh u coeff hcoeff ε hε hεsum hεlim
  obtain ⟨hInt, hTail⟩ :=
    avram_p3_comp8_original_BV_source_tail_L1_any_clock
      X hX hBV T L hL s hsm he
  exact ⟨κ, K, s, hκ, hsm, he, hmask, hInt, hTail⟩

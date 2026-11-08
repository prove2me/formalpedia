-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_compensator_integrand_eventually_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:05:44.440537+00:00
-- url     : https://prove2.me/submissions/2eedde46-9288-4f5e-ad32-511095e7d837

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (D : ℝ≥0 → Ω → ℝ) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) ∧
      ∀ (S : ℝ≥0) (p : ℝ≥0 × Ω) (z : ℝ)
        (w : ℝ → ℝ) (q : ℝ),
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let Z : ℝ≥0 × Ω → ℝ := fun r =>
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
        ∀ᶠ n : ℕ in atTop,
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc (a n) (b n) ∧ z < 0 then
            Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
            else 0) =
          (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
            Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
            else 0) := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
    avram_bv_meas7_allcap_full_predictable_compact_bands C hC
  refine ⟨a, b, ha, ha2, hab, hBand, hEvent, ?_⟩
  classical
  intro S p z w q
  dsimp only
  let Z : ℝ≥0 × Ω → ℝ := fun r =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        (Z p ∈ Icc (a n) (b n)) ↔
        (0 < Z p ∧ ENNReal.ofReal (Z p) < C) := by
    by_cases hInside : 0 < Z p ∧ ENNReal.ofReal (Z p) < C
    · obtain ⟨N, hN⟩ := hEvent (Z p) hInside.1 hInside.2
      filter_upwards [eventually_ge_atTop N] with n hn
      exact iff_of_true (hN n hn) hInside
    · have hOutside (n : ℕ) : ¬ Z p ∈ Icc (a n) (b n) := by
        intro hmem
        have hHalf : a n / 2 ≤ a n := by linarith [ha n]
        obtain ⟨hpos, hcap⟩ :=
          hBand n (show Z p ∈ Icc (a n / 2) (b n) from
            ⟨le_trans hHalf hmem.1, hmem.2⟩)
        exact hInside ⟨hpos, hcap⟩
      filter_upwards [] with n
      exact iff_of_false (hOutside n) hInside
  filter_upwards [hEventually] with n hMem
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
  change
    (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Z p ∈ Icc (a n) (b n) ∧ z < 0 then
      Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
      else 0) =
    (if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
      Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
      else 0)
  simp only [hMem, and_assoc]

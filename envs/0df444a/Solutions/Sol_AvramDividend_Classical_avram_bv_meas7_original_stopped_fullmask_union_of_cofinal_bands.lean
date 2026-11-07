-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_union_of_cofinal_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:15:54.920741+00:00
-- url     : https://prove2.me/submissions/01b02850-5e82-47d5-a702-43a590c6c3ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact exhaustion of the original ruin-stopped, pre-right-dividend reserve
interior by full compensation masks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hEvent : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (S : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    (⋃ n : ℕ, {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Z p ∈ Icc (a n) (b n)}) =
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} := by
  dsimp only
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    refine ⟨hn.1, ?_⟩
    have hHalf : a n / 2 ≤ a n := by linarith [ha n]
    exact hBand n ⟨le_trans hHalf hn.2.1, hn.2.2⟩
  · rintro ⟨ht, hpos, hcap⟩
    obtain ⟨N, hN⟩ := hEvent _ hpos hcap
    exact Set.mem_iUnion.mpr ⟨N, ht, hN N le_rfl⟩

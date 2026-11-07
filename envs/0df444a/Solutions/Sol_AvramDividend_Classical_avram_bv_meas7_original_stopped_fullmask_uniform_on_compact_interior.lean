-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_stopped_fullmask_uniform_on_compact_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:49:09.545189+00:00
-- url     : https://prove2.me/submissions/25c8abec-debb-49be-8dc9-d3f0416b740c

import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_allcap_full_predictable_compact_bands
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform eventual containment of every fixed original pre-dividend
compact interior reserve strip by the full compensation masks. -/
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
      ∀ c d : ℝ, 0 < c → c ≤ d →
        ENNReal.ofReal c < C → ENNReal.ofReal d < C →
        ∃ N : ℕ, ∀ n ≥ N, ∀ S : ℝ≥0,
          let τ : Ω → ℝ≥0 := fun ω =>
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let Z : ℝ≥0 × Ω → ℝ := fun p =>
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc c d} ⊆
          {p : ℝ≥0 × Ω |
            (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
            Z p ∈ Icc (a n) (b n)} := by
  obtain ⟨a, b, ha, ha2, hab, hBand, hEvent⟩ :=
    avram_bv_meas7_allcap_full_predictable_compact_bands C hC
  refine ⟨a, b, ha, ha2, hab, hBand, hEvent, ?_⟩
  intro c d hc hcd hccap hdcap
  obtain ⟨Nc, hNc⟩ := hEvent c hc hccap
  obtain ⟨Nd, hNd⟩ := hEvent d (lt_of_lt_of_le hc hcd) hdcap
  refine ⟨max Nc Nd, ?_⟩
  intro n hn S
  dsimp only
  intro p hp
  have hcn : c ∈ Icc (a n) (b n) :=
    hNc n (le_trans (Nat.le_max_left Nc Nd) hn)
  have hdn : d ∈ Icc (a n) (b n) :=
    hNd n (le_trans (Nat.le_max_right Nc Nd) hn)
  exact ⟨hp.1,
    ⟨le_trans hcn.1 hp.2.1, le_trans hp.2.2 hdn.2⟩⟩

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_uniform_grid_endpoint_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:27:22.498257+00:00
-- url     : https://prove2.me/submissions/e0b333bd-30c6-47d3-8562-56b95dfb745f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_physical_prefix_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The concrete original strictly-before-horizon uniform mesh carries
a ruin-stopped predictable compact pre-reserve mask at its exact endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T) (a b : ℕ → ℝ) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) ∧
      ∀ n : ℕ,
        let S : ℝ≥0 := u n (n + 1)
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        (∀ ω, τ ω ≤ S) ∧
        IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
        MeasurableSet[𝓕.rightCont.predictable] E ∧
        (∀ p ∈ E, Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
        (∀ p ∈ E, p.1 ≤ S) := by
  obtain ⟨u, hu0, huEnd, huMono, huWidth⟩ :=
    avram_p3_grid4_original_strict_prefix_uniform_physical_grid T hT
  refine ⟨u, hu0, huEnd, huMono, huWidth, ?_⟩
  intro n
  have hs : Real.toNNReal (T - T / ((n : ℝ) + 2)) = u n (n + 1) := by
    rw [← huEnd n]
    exact Real.toNNReal_coe
  have hPred :=
    avram_bv_meas7_original_physical_prefix_predictable_mask
      X x D hD T a b n
  dsimp only at hPred
  rw [hs] at hPred
  exact hPred

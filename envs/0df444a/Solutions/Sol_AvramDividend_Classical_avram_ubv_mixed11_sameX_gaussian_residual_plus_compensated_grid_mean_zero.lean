-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed11_sameX_gaussian_residual_plus_compensated_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T09:53:55.727782+00:00
-- url     : https://prove2.me/submissions/9eb47267-3792-4a00-bfbd-04e30cf6aeee

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical Gaussian residual and the original compensated finite jump
grid sum are jointly centred without requiring independence of their terms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (τ σ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (k : ℕ)
    (G : Ω → ℝ)
    (hGsource : ∀ ω,
      G ω = avram_p4_h_gaussian_intrinsic_truncated_residual X cut T ω)
    (hGI : Integrable G P) (hG0 : (∫ ω, G ω ∂P) = 0) :
    let J : Ω → ℝ := fun ω => ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)
    Integrable (G + J) P ∧
      (∫ ω, (G + J) ω ∂P) = 0 := by
  dsimp only
  obtain ⟨hJI, hJ0⟩ :=
    avram_ubv_loc6_original_arbitrary_compact_negative_grid_L1_centered
      X x Cap D hD n T cut grid hGrid hTime ε hε
      C hC hBand hCut N hActual H hH hHL2 τ σ hτeq hσstop hσle k
  constructor
  · exact hGI.add hJI
  · simp only [Pi.add_apply]
    rw [integral_add hGI hJI, hG0, hJ0, add_zero]

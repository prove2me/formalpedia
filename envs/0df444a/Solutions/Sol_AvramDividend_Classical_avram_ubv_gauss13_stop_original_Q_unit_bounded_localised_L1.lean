-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_unit_bounded_localised_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:02:06.389447+00:00
-- url     : https://prove2.me/submissions/043247fa-c7f7-47bd-a173-c6840ae41295

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Unit-bounded compact coefficients preserve the original quadratic Gaussian L¹ limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (Q : ℝ≥0 → Ω → ℝ)
    (hQsource : ∀ t ω, Q t ω =
      (X.X t ω - (t : ℝ) * X.c) ^ 2 - (t : ℝ) * X.σ ^ 2)
    (B : ℝ≥0) (hQB : Integrable (Q B) P)
    (σ : Ω → ℝ≥0) (T : ℕ → Ω → ℝ≥0)
    (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, (fun ω => Q (T n ω) ω) =ᵐ[P]
      condExp (ℋ n) P (Q B))
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => Q (T n ω) ω) atTop
        (nhds (Q (σ ω) ω)))
    (G : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) P)
    (hGunit : ∀ n ω, ‖G n ω‖ ≤ 1)
    (hGae : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => G n ω * Q (T n ω) ω -
        g ω * Q (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℕ → Ω → ℝ := fun n ω => Q (T n ω) ω
  have hUIC : UniformIntegrable
      (fun n => condExp (ℋ n) P (Q B)) 1 P :=
    hQB.uniformIntegrable_condExp hℋ
  have hUI : UniformIntegrable f 1 P :=
    (uniformIntegrable_congr_ae hCE).2 hUIC
  have hWeightedMeas : ∀ n,
      AEStronglyMeasurable (fun ω => G n ω * f n ω) P := by
    intro n
    exact (hGmeas n).mul (hUI.aestronglyMeasurable n)
  have hBound (n : ℕ) (ω : Ω) :
      ‖G n ω * f n ω‖ ≤ ‖f n ω‖ := by
    simpa [norm_mul] using
      mul_le_of_le_one_left (norm_nonneg (f n ω)) (hGunit n ω)
  have hUIWeighted : UniformIntegrable
      (fun n ω => G n ω * f n ω) 1 P := by
    refine ⟨hWeightedMeas, ?_, ?_⟩
    · intro ε hε
      obtain ⟨δ, hδpos, hSmall⟩ := hUI.unifIntegrable hε
      refine ⟨δ, hδpos, ?_⟩
      intro n s hs hμs
      calc
        eLpNorm (s.indicator (fun ω => G n ω * f n ω)) 1 P
            ≤ eLpNorm (s.indicator (f n)) 1 P := by
                apply eLpNorm_mono
                intro ω
                by_cases hw : ω ∈ s
                · simpa [Set.indicator_of_mem hw] using hBound n ω
                · simp [Set.indicator_of_notMem hw]
        _ ≤ ENNReal.ofReal ε := hSmall n s hs hμs
    · obtain ⟨C, hC⟩ := hUI.2.2
      refine ⟨C, fun n => ?_⟩
      exact (eLpNorm_mono (fun ω => hBound n ω)).trans (hC n)
  have hWeightedAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => G n ω * f n ω) atTop
        (nhds (g ω * Q (σ ω) ω)) := by
    filter_upwards [hGae, hAE] with ω hg hq
    exact hg.mul hq
  have hWeightedLimit :
      Integrable (fun ω => g ω * Q (σ ω) ω) P :=
    hUIWeighted.integrable_of_ae_tendsto hWeightedAE
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num : (1 : ℝ≥0∞) ≥ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    hWeightedMeas
    (memLp_one_iff_integrable.mpr hWeightedLimit)
    hUIWeighted.unifIntegrable hWeightedAE

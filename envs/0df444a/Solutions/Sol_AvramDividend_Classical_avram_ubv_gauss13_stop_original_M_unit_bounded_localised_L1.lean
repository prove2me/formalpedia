-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_M_unit_bounded_localised_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:19:19.793483+00:00
-- url     : https://prove2.me/submissions/7a81c9ab-39a7-4e0d-97b8-4300b6711f4d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Unit-bounded compact coefficients preserve the original linear Gaussian L¹ limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (M : ℝ≥0 → Ω → ℝ)
    (hMsource : ∀ t ω, M t ω =
      X.X t ω - (t : ℝ) * X.c)
    (B : ℝ≥0) (hMB : Integrable (M B) P)
    (σ : Ω → ℝ≥0) (T : ℕ → Ω → ℝ≥0)
    (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, (fun ω => M (T n ω) ω) =ᵐ[P]
      condExp (ℋ n) P (M B))
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => M (T n ω) ω) atTop
        (nhds (M (σ ω) ω)))
    (G : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) P)
    (hGunit : ∀ n ω, ‖G n ω‖ ≤ 1)
    (hGae : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => G n ω * M (T n ω) ω -
        g ω * M (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℕ → Ω → ℝ := fun n ω => M (T n ω) ω
  have hUIC : UniformIntegrable
      (fun n => condExp (ℋ n) P (M B)) 1 P :=
    hMB.uniformIntegrable_condExp hℋ
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
        (nhds (g ω * M (σ ω) ω)) := by
    filter_upwards [hGae, hAE] with ω hg hq
    exact hg.mul hq
  have hWeightedLimit :
      Integrable (fun ω => g ω * M (σ ω) ω) P :=
    hUIWeighted.integrable_of_ae_tendsto hWeightedAE
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num : (1 : ℝ≥0∞) ≥ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    hWeightedMeas
    (memLp_one_iff_integrable.mpr hWeightedLimit)
    hUIWeighted.unifIntegrable hWeightedAE


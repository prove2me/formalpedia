-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_terminal_condexp_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:42:44.166195+00:00
-- url     : https://prove2.me/submissions/32c53d01-9681-4726-8640-6aee9c6cb3eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original compensated Gaussian squares have an L¹ physical-clock limit
when all ceilings are conditional samples of one integrable terminal square. -/
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
        (nhds (Q (σ ω) ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => Q (T n ω) ω - Q (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hUIC : UniformIntegrable
      (fun n => condExp (ℋ n) P (Q B)) 1 P :=
    hQB.uniformIntegrable_condExp hℋ
  have hUI : UniformIntegrable
      (fun n ω => Q (T n ω) ω) 1 P :=
    (uniformIntegrable_congr_ae hCE).2 hUIC
  have hZI : Integrable (fun ω => Q (σ ω) ω) P :=
    hUI.integrable_of_ae_tendsto hAE
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num : (1 : ℝ≥0∞) ≥ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (fun n => hUI.aestronglyMeasurable n)
    (memLp_one_iff_integrable.mpr hZI)
    hUI.unifIntegrable hAE

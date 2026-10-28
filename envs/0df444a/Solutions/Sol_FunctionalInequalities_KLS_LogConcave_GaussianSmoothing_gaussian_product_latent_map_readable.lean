-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_latent_map_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:36:40.960044+00:00
-- url     : https://prove2.me/submissions/9e888a38-f969-4624-9962-90dc8afe56e2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage

noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem solution (ρ μ : Measure E) [IsProbabilityMeasure ρ]
    (g : E → E) (hg : Measurable g) (hmap : ρ.map g = μ)
    (S : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    (ρ.prod (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)).map (fun p => S (g p.1) + p.2) =
      FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw (μ.map S) s := by
  let γ : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let _ : IsProbabilityMeasure γ := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hp : (ρ.map (fun x => S (g x))).prod γ =
      (ρ.prod γ).map (Prod.map (fun x => S (g x)) id) := by
    simpa only [Measure.map_id, Function.comp_def] using Measure.map_prod_map ρ γ
      (S.continuous.measurable.comp hg) measurable_id
  unfold FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.smoothedLaw Measure.conv
  rw [← hmap, Measure.map_map S.continuous.measurable hg]
  change (ρ.prod γ).map (fun p => S (g p.1) + p.2) =
    ((ρ.map (fun x => S (g x))).prod γ).map (fun p => p.1 + p.2)
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

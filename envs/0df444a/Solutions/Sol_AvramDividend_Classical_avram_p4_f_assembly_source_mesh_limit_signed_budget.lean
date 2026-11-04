-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_source_mesh_limit_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:18:50.304422+00:00
-- url     : https://prove2.me/submissions/4c33f139-abe0-42a6-8e48-1669f315dce3

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Preserve joint nonpositivity through a.e. source mesh limits while
    retaining the true stopped terminal and full Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (Mseq Gseq Hseq : ℕ → Ω → ℝ) (M G H : Ω → ℝ)
    (hupper : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Term ω + Cash ω ≤ w x + Mseq k ω + Gseq k ω + Hseq k ω)
    (hsign : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Gseq k ω + Hseq k ω ≤ 0)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Mseq k ω) atTop (𝓝 (M ω)) ∧
      Tendsto (fun k : ℕ => Gseq k ω) atTop (𝓝 (G ω)) ∧
      Tendsto (fun k : ℕ => Hseq k ω) atTop (𝓝 (H ω))) :
    (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
    (∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  constructor
  · filter_upwards [hsign, hconv] with ω hs hc
    have ht :
        Tendsto (fun k : ℕ => Gseq k ω + Hseq k ω)
          atTop (𝓝 (G ω + H ω)) := hc.2.1.add hc.2.2
    exact le_of_tendsto ht (Filter.Eventually.of_forall hs)
  · exact avram_wave7_08_source_original_stopped_ito_mesh_ae_limit_upper
      X q x w D τ W Cash Term hW hCash hTerm
      Mseq Gseq Hseq M G H hupper hconv

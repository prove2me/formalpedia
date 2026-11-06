-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_pathwise_left_mesh_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:18:41.23071+00:00
-- url     : https://prove2.me/submissions/620854e2-098c-4dc9-ac63-a9ee784f577d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original discounted terminal is recovered along observation meshes
that may depend on the sample path. This applies to the stopped crossing
index once the strict-left mesh convergence is verified pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω n, u ω n < t)
    (huLimit : ∀ ω, Tendsto (u ω) atTop (𝓝 t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n : ℕ =>
        Real.exp (-(q * (u ω n : ℝ))) *
          w (x + X.X (u ω n) ω - rightLimit D (u ω n) ω))
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by
  filter_upwards [avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
    X x C D hD w hw_cont q t ht] with ω hTerminal
  intro hSurvive
  have huWithin : Tendsto (u ω) atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨huLimit ω,
      Filter.Eventually.of_forall (fun n => hu ω n)⟩
  exact (hTerminal hSurvive).comp huWithin

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys45_original_finite_activity_ruin_clipped_compact_fibre_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:37:26.404363+00:00
-- url     : https://prove2.me/submissions/3ff03a11-ecbf-414e-a80b-be783eb04929

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original ruin-clipped compact reserve kernel has integrable physical compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  intro τ E H
  obtain ⟨hτBound, hτStop, hEm, hEband, hEtime⟩ :=
    avram_p3_g_localise_original_ruin_stopped_compact_previsible
      X x D hD T a b
  have hb : 0 ≤ b := le_trans ha hab
  have hRegion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ≤ b := by
    intro p hp
    exact (hEband p hp).2
  simpa only [H] using
    (avram_bvb_phys41_original_finite_activity_predictable_physical_fibre_L1
      X x D hD w hw_cont hw_neg q hq b hb hActivity T E hEm hRegion)

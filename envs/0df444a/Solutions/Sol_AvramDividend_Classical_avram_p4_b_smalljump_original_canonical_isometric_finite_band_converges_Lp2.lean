-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_isometric_finite_band_converges_Lp2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:09.580194+00:00
-- url     : https://prove2.me/submissions/cfbcab66-b9cd-4cbf-820f-9e39e02bc9dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original Lévy predictable space, the canonical neighbourhoods
(-1/(n+1),0) may be removed from an isometric L2 integral without changing
the L2 limit. The source isometry remains an explicit hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2;
      let hML : MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) :=
        avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
          X μ g hgm hgL2;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      Tendsto (fun n : ℕ =>
        let A : Set ((ℝ≥0 × Ω) × ℝ) :=
          {p | p.2 ∉ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) 0}
        I ((hML.indicator (measurableSet_Ioo.preimage measurable_snd).compl).toLp
          (A.indicator G))) atTop (𝓝 (I (hML.toLp G)))) := by
  let B : ℕ → Set ℝ := fun n =>
    Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)
  have hBm : ∀ n, MeasurableSet (B n) := fun n => measurableSet_Ioo
  obtain ⟨hBanti, hBempty⟩ :=
    avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
  simpa only [B] using
    (avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
      X μ g hgm hgL2 B hBm hBanti hBempty)

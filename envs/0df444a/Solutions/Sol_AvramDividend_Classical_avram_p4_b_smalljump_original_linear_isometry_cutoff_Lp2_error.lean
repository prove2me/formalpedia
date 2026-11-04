-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:14.611311+00:00
-- url     : https://prove2.me/submissions/d3e48da3-8d50-4817-b532-876209596c2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-source predictable linear small-jump L2 cutoff error under an
explicit norm-preserving compensated stochastic-integral map. -/
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
      ∀ (A : Set ((ℝ≥0 × Ω) × ℝ)) (hA : MeasurableSet A)
        (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      ‖I ((hML.indicator hA).toLp (A.indicator G)) -
        I (hML.toLp G)‖ ≤
          (eLpNorm (Aᶜ.indicator G) (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))).toReal) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro G hML A hA I hIso
  let mprod : Measure ((ℝ≥0 × Ω) × ℝ) := (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))
  let cut : Lp ℝ (2 : ℝ≥0∞) mprod :=
    (hML.indicator hA).toLp (A.indicator G)
  let full : Lp ℝ (2 : ℝ≥0∞) mprod := hML.toLp G
  have hcut : ‖cut - full‖ ≤
      ‖(hML.indicator hA.compl).toLp (Aᶜ.indicator G)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hML.indicator hA).coeFn_toLp,
      hML.coeFn_toLp,
      (hML.indicator hA.compl).coeFn_toLp,
      Lp.coeFn_sub cut full] with p ha hf hc hs
    have hpoint : ‖A.indicator G p - G p‖ ≤
        ‖Aᶜ.indicator G p‖ := by
      by_cases hp : p ∈ A <;> simp [Set.indicator, hp, norm_neg]
    calc
      ‖(cut - full) p‖ = ‖cut p - full p‖ := congrArg norm hs
      _ = ‖A.indicator G p - G p‖ := by rw [ha, hf]
      _ ≤ ‖Aᶜ.indicator G p‖ := hpoint
      _ = ‖((hML.indicator hA.compl).toLp (Aᶜ.indicator G)) p‖ :=
        (congrArg norm hc).symm
  calc
    ‖I cut - I full‖ = ‖cut - full‖ := by rw [← map_sub, hIso]
    _ ≤ ‖(hML.indicator hA.compl).toLp (Aᶜ.indicator G)‖ := hcut
    _ = (eLpNorm (Aᶜ.indicator G) (2 : ℝ≥0∞) mprod).toReal :=
      Lp.norm_toLp (Aᶜ.indicator G) (hML.indicator hA.compl)

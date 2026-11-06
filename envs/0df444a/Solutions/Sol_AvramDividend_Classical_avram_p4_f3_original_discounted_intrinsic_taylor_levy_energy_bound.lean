-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_levy_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:02:13.131399+00:00
-- url     : https://prove2.me/submissions/8270274e-e7e8-4549-8c86-f0bbc5c21057

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Expected Lévy-intensity energy controls each exact discounted original small-jump Taylor kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ p : ℝ≥0 × Ω,
        (∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal (|A p *
            SpectrallyNegativeLevy.generatorIntegrand f (U p) z|)
            ∂X.ν) ≤
          ENNReal.ofReal C *
            (∫⁻ z in Ioo (-r) (0 : ℝ),
              ENNReal.ofReal (z ^ 2) ∂X.ν)) := by
  classical
  obtain ⟨r, C, hr, hrle, hC, hPoint⟩ :=
    avram_p4_f3_original_discounted_intrinsic_taylor_uniform_quadratic
      X x D f a l u hl hlu hu hf T q hq
  refine ⟨r, C, hr, hrle, hC, ?_⟩
  dsimp only
  intro p
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    let y := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    if y ∈ Icc l u then y else l
  let A : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  change (∫⁻ z in Ioo (-r) (0 : ℝ),
    ENNReal.ofReal (|A p *
      SpectrallyNegativeLevy.generatorIntegrand f (U p) z|) ∂X.ν) ≤
    ENNReal.ofReal C *
      (∫⁻ z in Ioo (-r) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν)
  have hmeas : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2)) := by
    fun_prop
  calc
    _ ≤ ∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal (C * z ^ 2) ∂X.ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact ENNReal.ofReal_le_ofReal (hPoint p z hz)
    _ = ENNReal.ofReal C *
        (∫⁻ z in Ioo (-r) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν) := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul (ENNReal.ofReal C) hmeas

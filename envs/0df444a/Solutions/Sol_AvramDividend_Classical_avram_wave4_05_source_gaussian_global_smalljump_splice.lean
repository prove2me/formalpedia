-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_gaussian_global_smalljump_splice
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:50:02.607072+00:00
-- url     : https://prove2.me/submissions/c380ba31-eb8f-47e0-8f27-b80902e38bd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_crossing_weighted_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_interior_generator_weighted_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual compensated source kernel, crossing and interior joined on every
    positive reserve, with the true Gaussian source crossing coefficient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (F : ℝ → ℝ)
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ : ℝ, 0 ≤ θ →
        Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume →
        ∀ r : ℝ, 0 < r → r < 1 →
          IntegrableOn
            (fun x : ℝ => Real.exp (-θ * x) *
              |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
            (Ioi (0 : ℝ)) volume ∧
          (∫ x in Ioi (0 : ℝ),
            Real.exp (-θ * x) *
              |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
            (C + (∫ u : ℝ, Real.exp (-θ * u) * |F u|) / 2) * r ^ 2 := by
  obtain ⟨C, hC, hcross⟩ :=
    avram_wave3_05_gaussian_crossing_weighted_quadratic X hX q hq W hW hσ
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  refine ⟨C, hC, ?_⟩
  intro θ hθ hFi r hr hr1
  let f : ℝ → ℝ := fun x =>
    Real.exp (-θ * x) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|
  have hcr0 := hcross θ hθ (-r) (by linarith) (by linarith)
  have hcr : IntegrableOn f (Ioo (0 : ℝ) r) volume ∧
      (∫ x in Ioo (0 : ℝ) r, f x) ≤ C * r ^ 2 := by
    change IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioo (0 : ℝ) r) volume ∧
      (∫ x in Ioo (0 : ℝ) r, Real.exp (-θ * x) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤ C * r ^ 2
    have hexp (x : ℝ) : Real.exp (-(θ * x)) = Real.exp (-θ * x) := by
      congr 1
      ring
    simpa only [neg_neg, neg_sq, hexp] using hcr0
  have hin0 := avram_wave4_05_source_interior_generator_weighted_quadratic
    W F hC2 hFpoint r θ hr hr1 hθ hFc hFm hFi
  have hin : IntegrableOn f (Ioi r) volume ∧
      (∫ x in Ioi r, f x) ≤
        (r ^ 2 / 2) * (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := hin0
  have hci : IntegrableOn f (Ici r) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hin.1
  have hdisj : Disjoint (Ioo (0 : ℝ) r) (Ici r) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy) hx.2
  have hglob : IntegrableOn f (Ioi (0 : ℝ)) volume := by
    rw [← Set.Ioo_union_Ici_eq_Ioi hr]
    exact (integrableOn_union).2 ⟨hcr.1, hci⟩
  have hpart : (∫ x in Ioi (0 : ℝ), f x) =
      (∫ x in Ioo (0 : ℝ) r, f x) + (∫ x in Ioi r, f x) := by
    rw [← Set.Ioo_union_Ici_eq_Ioi hr]
    rw [setIntegral_union hdisj measurableSet_Ici hcr.1 hci]
    rw [integral_Ici_eq_integral_Ioi]
  refine ⟨hglob, ?_⟩
  change (∫ x in Ioi (0 : ℝ), f x) ≤
    (C + (∫ u : ℝ, Real.exp (-θ * u) * |F u|) / 2) * r ^ 2
  rw [hpart]
  nlinarith [hcr.2, hin.2]

-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_two_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:29:38.604724+00:00
-- url     : https://prove2.me/submissions/ad53c70f-c009-42e0-bde9-71bad76a9100

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 W (Ioi 0) := by
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_gaussian X q hq hσ
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  obtain ⟨a, β, K, g, ha, hKi, hgc, hgC1, hVEq, hgEq⟩ :=
    gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilted_scale_continuous X q hq W hW hσ φ V hV
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C :=
    gaussian_esscher_tilted_scale_locally_bounded
      X q hq W hW hσ φ hφ V hV
  have hVC2 : ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) :=
    causal_volterra_C2_of_C1_derivative_resolvent
      K g V a β ha hKi hVc hVb hVEq hgc hgC1 hgEq
  exact esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two
    φ W V hVC2 hV

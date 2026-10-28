-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_finite_renewal_cumulative_representation_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:10:18.665812+00:00
-- url     : https://prove2.me/submissions/e09ae099-23b3-4ec9-8133-bf45af2430bd

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_finite_laplace_package_ac
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
Identify the positive-axis absolutely continuous geometric renewal
cumulative with the Esscher tilted BV scale function.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal) := by
  obtain ⟨β, b, hβpos, hβfinite, hβac, hfin, hlap⟩ :=
    bv_esscher_root_finite_laplace_package_ac
      X hX q hq W hW hbv φ hφ hroot
  let g : ℝ → ℝ := fun x => (β (Iic x)).toReal
  have hgmono : Monotone g := by
    intro x y hxy
    exact ENNReal.toReal_mono (hfin y)
      (measure_mono (Iic_subset_Iic.mpr hxy))
  have hgmeas : AEMeasurable g (volume.restrict (Ioi (0 : ℝ))) :=
    hgmono.measurable.aemeasurable
  have hgright :
      ∀ x : ℝ, 0 < x → ContinuousWithinAt g (Ici x) x := by
    intro x hx
    exact rightContinuous_cumulative_toReal_of_finite β hfin x
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x := by
    intro x hx
    exact ENNReal.toReal_nonneg
  have htiltcont :
      ContinuousOn (fun x : ℝ => Real.exp (-(φ * x)) * W x)
        (Ioi (0 : ℝ)) := by
    have hexp : ContinuousOn (fun x : ℝ => Real.exp (-(φ * x)))
        (Ioi (0 : ℝ)) := by fun_prop
    have hWcont : ContinuousOn W (Ioi (0 : ℝ)) :=
      hW.2.2.1.mono (by
        intro x hx
        exact le_of_lt (show (0 : ℝ) < x from hx))
    exact hexp.mul hWcont
  have htiltnonneg :
      ∀ x : ℝ, 0 < x → 0 ≤ Real.exp (-(φ * x)) * W x := by
    intro x hx
    exact mul_nonneg (Real.exp_pos _).le (hW.2.1 x (le_of_lt hx))
  have heq :
      ∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = g x :=
    continuous_rightContinuous_Ioi_eq_of_laplace_eq
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) g b
      htiltcont hgright hgmeas htiltnonneg hgnonneg (by
        intro θ hθ
        simpa [g] using hlap θ hθ)
  exact ⟨β, hβpos, hβfinite, hβac, heq⟩

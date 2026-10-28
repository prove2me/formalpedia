-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_volterra_origin_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:49:08.717994+00:00
-- url     : https://prove2.me/submissions/cc752352-db75-47fa-a8e3-91e1857364e3

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_deriv_right_limit
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- A right-derivative limit and origin normalisation supply a vanishing Volterra remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    W 0 = 1 / X.drift ∧
      ∃ G : ℝ → ℝ,
        ContinuousWithinAt W (Ioi (0 : ℝ)) 0 ∧
        Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
        (∀ x : ℝ, 0 < x →
          deriv W x =
            ((q + (X.ν (Iio (0 : ℝ))).toReal) / X.drift) * W x -
              G x / X.drift) := by
  let d : ℝ := X.drift
  let l : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hd : d ≠ 0 := ne_of_gt (bv_standing_drift_pos X hX hBV).1
  have h0 : W 0 = 1 / d := bv_scale_origin_eq_inv_drift X hX q hq W hW hBV
  have hderiv : Tendsto (fun x : ℝ => deriv W x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((q + l) / d ^ 2)) :=
    bv_finite_activity_scale_deriv_right_limit X hX q hq W hW hBV hFinite
  have hcont : ContinuousWithinAt W (Ioi (0 : ℝ)) 0 := by
    exact (hW.2.2.1.continuousWithinAt (by simp)).mono (by
      intro x hx
      exact le_of_lt (mem_Ioi.mp hx))
  let G : ℝ → ℝ := fun x => (q + l) * W x - d * deriv W x
  have hGlim : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((q + l) * W 0 - d * ((q + l) / d ^ 2))) := by
    dsimp [G]
    exact (tendsto_const_nhds.mul hcont).sub (tendsto_const_nhds.mul hderiv)
  have hGzero : (q + l) * W 0 - d * ((q + l) / d ^ 2) = 0 := by
    rw [h0]
    field_simp
    ring
  refine ⟨by simpa [d] using h0, G, hcont, ?_, ?_⟩
  · simpa only [hGzero] using hGlim
  · intro x hx
    change deriv W x = ((q + l) / d) * W x -
      ((q + l) * W x - d * deriv W x) / d
    field_simp [hd]
    ring

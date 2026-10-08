-- Prove2me | solution 4 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:14:19.491813+00:00
-- url     : https://prove2.me/submissions/92a7fe94-2d91-4f92-9f71-6519dd6c6b9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Derivative coercivity directly from the Esscher excursion-tail identity.
This avoids both the broad C1 theorem and tilted-normalisation monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  have hW1 : 0 < W 1 :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW 1 (by norm_num)
  let d : ℝ := φ * W 1
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos hφ hW1
  have hderiv_ge : ∀ x : ℝ, 1 ≤ x → d ≤ deriv W x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    rw [hrepr x hxpos]
    have hmono : W 1 ≤ W x := by
      exact hW.2.2.2.1
        (show (1 : ℝ) ∈ Ici 0 by norm_num)
        (show x ∈ Ici 0 by exact hxpos.le) hx
    have hWx : 0 ≤ W x := hW.2.1 x hxpos.le
    have htail : 0 ≤ μ.real (Ici x) := measureReal_nonneg
    dsimp [d]
    calc
      φ * W 1 ≤ φ * W x := mul_le_mul_of_nonneg_left hmono hφ.le
      _ ≤ W x * (φ + μ.real (Ici x)) := by
        rw [mul_add]
        nlinarith [mul_nonneg hWx htail]
  let k : ℝ := φ * d
  let c : ℝ := φ * (W 1 - d)
  have hk : 0 < k := by
    dsimp [k]
    exact mul_pos hφ hd
  have hge :
      ∀ᶠ x : ℝ in atTop, k * x + c ≤ deriv W x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hcont : ContinuousOn W (Icc 1 x) :=
      hW.2.2.1.mono (by
        intro y hy
        exact le_trans (by norm_num) hy.1)
    have hdiffI :
        DifferentiableOn ℝ W (interior (Icc 1 x)) := by
      intro y hy
      have hy' : y ∈ Ioo 1 x := by
        simpa only [interior_Icc] using hy
      exact (hdiff y (lt_trans (by norm_num) hy'.1)).differentiableWithinAt
    have hlow :
        ∀ y ∈ interior (Icc 1 x), d ≤ deriv W y := by
      intro y hy
      have hy' : y ∈ Ioo 1 x := by
        simpa only [interior_Icc] using hy
      exact hderiv_ge y hy'.1.le
    have hsec :
        (x - 1) * d ≤ W x - W 1 := by
      simpa only [mul_comm] using
        (convex_Icc (1 : ℝ) x).mul_sub_le_image_sub_of_le_deriv
          hcont hdiffI hlow
          1 ⟨le_rfl, hx⟩ x ⟨hx, le_rfl⟩ hx
    have hWxlow : W 1 + (x - 1) * d ≤ W x := by
      linarith
    have htail : 0 ≤ μ.real (Ici x) := measureReal_nonneg
    have hWx : 0 ≤ W x := hW.2.1 x hxpos.le
    have hphi :
        φ * W x ≤ deriv W x := by
      rw [hrepr x hxpos]
      rw [mul_add]
      nlinarith [mul_nonneg hWx htail]
    have hmain :
        φ * (W 1 + (x - 1) * d) ≤ deriv W x := by
      exact le_trans (mul_le_mul_of_nonneg_left hWxlow hφ.le) hphi
    dsimp [k, c]
    nlinarith
  have hlin : Tendsto (fun x : ℝ => k * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hk).2 tendsto_id
  have hmodel : Tendsto (fun x : ℝ => k * x + c) atTop atTop :=
    Tendsto.atTop_add hlin tendsto_const_nhds
  exact tendsto_atTop_mono' atTop hge hmodel

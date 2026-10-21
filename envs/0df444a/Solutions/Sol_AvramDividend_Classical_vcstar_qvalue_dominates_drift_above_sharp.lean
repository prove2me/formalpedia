-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_qvalue_dominates_drift_above_sharp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:20:56.03919+00:00
-- url     : https://prove2.me/submissions/5c3e6c72-b978-442b-8b26-3dd24b743273

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg_of_pos
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The drift is dominated by the discounted barrier value above the threshold
`c* + max 0 (c / q)`.

Above the barrier level the barrier value is affine with slope one, namely
`x - c* + W (c*) / W'(c*)`.  The threshold assumption bounds the drift `c` by
`q * (x - c*)`, and the normalising factor `W (c*) / W'(c*)` is non-negative
because the scale function and its derivative are non-negative on the
positive half-line.  Hence `q * v_{c*}(x) ≥ c`.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.c ≤ q * vcstar W x := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 < a := hpos
  have hd : 0 ≤ deriv W a :=
    scaleFunction_deriv_nonneg_of_pos X q W hW a ha
  have hw : 0 ≤ W a := hW.2.1 a (le_of_lt ha)
  have hdiv : divE (W a) (scaleDeriv W a) = W a / deriv W a := by
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp [divE, scaleDeriv, ha0]
  have hk : 0 ≤ divE (W a) (scaleDeriv W a) := by
    rw [hdiv]
    exact div_nonneg hw hd
  have hratio : X.c / q ≤ x - a := by
    have hm : X.c / q ≤ max 0 (X.c / q) := le_max_right _ _
    dsimp [a] at *
    linarith
  have hc : X.c ≤ (x - a) * q :=
    (div_le_iff₀ hq).mp hratio
  change X.c ≤ q * (barrierValue W a x)
  have hx0 : ¬ x < 0 := not_lt.mpr (le_trans (le_of_lt ha) (le_of_lt hx))
  have hxa : ¬ x ≤ a := not_le.mpr hx
  simp only [barrierValue, if_neg hx0, if_neg hxa]
  have hqk : 0 ≤ q * divE (W a) (scaleDeriv W a) :=
    mul_nonneg (le_of_lt hq) hk
  nlinarith

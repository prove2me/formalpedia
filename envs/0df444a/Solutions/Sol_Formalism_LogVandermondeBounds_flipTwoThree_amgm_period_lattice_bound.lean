-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:49.539019+00:00
-- url     : https://prove2.me/submissions/feef19a6-3903-4fe3-8a8b-634dba4ed0d6

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution : AmgmSumLowerBoundOfProd := by
  intro f v x hf hv hx hprod
  have hf0 : (0:ℝ) < f := by exact_mod_cast hf
  have hfne : f ≠ 0 := by omega
  have hw : ∑ _i : Fin f, (f:ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have amgm := Real.geom_mean_le_arith_mean_weighted (s := univ) (fun _ => (f:ℝ)⁻¹) x
    (fun _ _ => by positivity) hw (fun i _ => (hx i).le)
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hx i).le)] at amgm
  have hlow : (2 * v)⁻¹ ≤ (∏ i, x i) ^ ((f:ℝ)⁻¹) := by
    have h0 : (0:ℝ) ≤ ((2 * v) ^ f)⁻¹ := by positivity
    have := Real.rpow_le_rpow h0 hprod (by positivity : (0:ℝ) ≤ (f:ℝ)⁻¹)
    rw [← inv_pow, Real.pow_rpow_inv_natCast (by positivity) hfne] at this
    exact this
  have h := hlow.trans amgm
  rw [← Finset.mul_sum] at h
  have e : (f:ℝ) / v = 2 * f * (2 * v)⁻¹ := by field_simp
  rw [e]
  calc 2 * (f:ℝ) * (2 * v)⁻¹ ≤ 2 * f * ((f:ℝ)⁻¹ * ∑ i, x i) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ∑ i, x i := by field_simp
end Formalism.LogVandermondeBounds.flipTwoThree

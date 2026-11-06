-- Prove2me | solution 1 for FiniteEnergyPlane.exists_eq_zero_of_hasLoopWind_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-05T20:24:34.505668+00:00
-- url     : https://prove2.me/submissions/729a3ca5-8d76-45f0-bfdb-dd59f960796f

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_eq_sum
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique

open Metric Filter Topology
open scoped Real

namespace FiniteEnergyPlane

/-- Let `h` have nonzero winding number along the circle of radius `R` about `c`, and let `g` be
continuous on the closed disc with `‖g - h‖ < ‖h‖` on that circle. Then `g` has a zero in the
closed disc. -/
theorem exists_eq_zero_of_hasLoopWind_of_norm_sub_lt_aux (g h : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (closedBall c R)) (k : ℤ) (hk : k ≠ 0)
    (hw : HasLoopWind (fun t => h (c + ccwLoop R t)) k)
    (hclose : ∀ t : ℝ, ‖g (c + ccwLoop R t) - h (c + ccwLoop R t)‖ < ‖h (c + ccwLoop R t)‖) :
    ∃ z ∈ closedBall c R, g z = 0 := by
  by_contra hno
  push_neg at hno
  have hloopc : Continuous (ccwLoop R) := by
    unfold ccwLoop
    fun_prop
  have hmem : ∀ t : ℝ, c + ccwLoop R t ∈ closedBall c R := by
    intro t
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    unfold ccwLoop
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  have hper : Function.Periodic (ccwLoop R) 1 := by
    intro t
    unfold ccwLoop
    congr 1
    have : (((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
        ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hfc : Continuous (fun t => g (c + ccwLoop R t)) :=
    hg.comp_continuous (continuous_const.add hloopc) hmem
  have hfp : Function.Periodic (fun t => g (c + ccwLoop R t)) 1 := by
    intro t
    simp only [hper t]
  have hpos : ∀ t, 0 < (starRingEnd ℂ (h (c + ccwLoop R t)) * g (c + ccwLoop R t)).re := by
    intro t
    set a := h (c + ccwLoop R t)
    set b := g (c + ccwLoop R t)
    have hlt : ‖b - a‖ < ‖a‖ := hclose t
    have hapos : 0 < ‖a‖ := lt_of_le_of_lt (norm_nonneg _) hlt
    have h1 : starRingEnd ℂ a * b = (‖a‖ ^ 2 : ℝ) + starRingEnd ℂ a * (b - a) := by
      rw [mul_sub, Complex.conj_mul', ]
      push_cast
      ring
    rw [h1, Complex.add_re, Complex.ofReal_re]
    have h2 : -(‖a‖ * ‖b - a‖) ≤ (starRingEnd ℂ a * (b - a)).re := by
      have := Complex.abs_re_le_norm (starRingEnd ℂ a * (b - a))
      rw [norm_mul, Complex.norm_conj] at this
      exact (abs_le.1 this).1
    nlinarith
  have hf : HasLoopWind (fun t => g (c + ccwLoop R t)) k :=
    hasLoopWind_of_re_conj_mul_pos hw hfc hfp hpos
  have h0 := hasLoopWind_ccwLoop_eq_sum g ∅ c R hR (by simp) (by simpa using hg)
    (fun z hz => hno z (by simpa using hz)) (fun _ => 0) (by simp)
  simp only [Finset.sum_empty] at h0
  exact hk (hasLoopWind_unique hf h0)

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric

theorem solution (g h : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (closedBall c R)) (k : ℤ) (hk : k ≠ 0)
    (hw : HasLoopWind (fun t => h (c + ccwLoop R t)) k)
    (hclose : ∀ t : ℝ, ‖g (c + ccwLoop R t) - h (c + ccwLoop R t)‖ < ‖h (c + ccwLoop R t)‖) :
    ∃ z ∈ closedBall c R, g z = 0 :=
  FiniteEnergyPlane.exists_eq_zero_of_hasLoopWind_of_norm_sub_lt_aux g h c R hR hg k hk hw hclose

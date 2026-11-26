-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_closing_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:54.381094+00:00
-- url     : https://prove2.me/submissions/6279d4b2-e201-4e74-834f-b968557ec10f

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_log_lipschitz_upper
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {D : Set ℂ} {a : ℂ} {L : ℂ → ℂ} {C : ℝ≥0}
    (hL : LipschitzOnWith C L D)
    (hclose : ∀ z ∈ D, ‖L z - L a‖ ≤ 1)
    (hinv : ∀ z ∈ D, Complex.exp (L z) = z) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
      LipschitzOnWith C ψ D ∧ MapsTo ψ D (ball (x : ℂ) 8) ∧
      ∀ z ∈ D, expIterate 2 (ψ z) = z := by
  refine ⟨|(L a).re| + 2 * Real.pi + 4, fun x hx => ?_⟩
  -- A single integer translation works uniformly for the whole bounded logarithm branch.
  let k : ℤ := ⌈(2 * Real.exp x - (L a).im) / (2 * Real.pi)⌉
  let T : ℂ → ℂ := fun z => L z + (k : ℂ) * (2 * Real.pi * Complex.I)
  have hp : 0 < 2 * Real.pi := by positivity
  have hxexp : 1 ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x, abs_nonneg (L a).re, Real.pi_pos]
  have him : ∀ z, (T z).im = (L z).im + (k : ℝ) * (2 * Real.pi) := by
    intro z
    simp [T, Complex.mul_im, Complex.mul_re]
  have hre : ∀ z, (T z).re = (L z).re := by intro z; simp [T]
  have hklo : 2 * Real.exp x - (L a).im ≤ (k : ℝ) * (2 * Real.pi) :=
    (div_le_iff₀ hp).mp (Int.le_ceil _)
  have hkhi : (k : ℝ) * (2 * Real.pi) < 2 * Real.exp x - (L a).im + 2 * Real.pi := by
    have h := mul_lt_mul_of_pos_right
      (Int.ceil_lt_add_one ((2 * Real.exp x - (L a).im) / (2 * Real.pi))) hp
    simpa only [add_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul] using h
  -- The translated branch stays high in the upper half-plane, where log is 1-Lipschitz.
  have htlo : ∀ z ∈ D, Real.exp x ≤ (T z).im := by
    intro z hz
    have h := (Complex.abs_im_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_im] at h
    rw [him]
    linarith [(abs_le.mp h).1]
  have hthi : ∀ z ∈ D, (T z).im < 2 * Real.exp x + 2 * Real.pi + 1 := by
    intro z hz
    have h := (Complex.abs_im_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_im] at h
    rw [him]
    linarith [(abs_le.mp h).2]
  have htre : ∀ z ∈ D, |(T z).re| ≤ |(L a).re| + 1 := by
    intro z hz
    rw [hre]
    have h := (Complex.abs_re_le_norm (L z - L a)).trans (hclose z hz)
    simp only [Complex.sub_re] at h
    calc |(L z).re| = |((L z).re - (L a).re) + (L a).re| := by congr 1; ring
      _ ≤ |(L z).re - (L a).re| + |(L a).re| := by
        simpa only [Real.norm_eq_abs] using norm_add_le ((L z).re - (L a).re) (L a).re
      _ ≤ _ := by linarith
  have htpos : ∀ z ∈ D, 0 < (T z).im := fun z hz => (Real.exp_pos x).trans_le (htlo z hz)
  have htne : ∀ z ∈ D, T z ≠ 0 := by
    intro z hz heq
    have := htpos z hz
    simp [heq] at this
  have hTlip : LipschitzOnWith C T D := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro z hz w hw
    simpa [T] using hL.norm_sub_le hz hw
  -- The resulting branch has a uniform Lipschitz bound and is a right inverse of exp squared.
  refine ⟨Complex.log ∘ T, ?_, ?_, ?_⟩
  · simpa using log_lipschitz_upper.comp hTlip (fun z hz => hxexp.trans (htlo z hz))
  · intro z hz
    have hnlo : Real.exp x ≤ ‖T z‖ := (htlo z hz).trans (Complex.im_le_norm _)
    have hnhi : ‖T z‖ ≤ Real.exp (x + 2) := by
      have h := Complex.norm_le_abs_re_add_abs_im (T z)
      rw [abs_of_pos (htpos z hz)] at h
      have hmx : |(L a).re| + 2 * Real.pi + 2 ≤ Real.exp x := by
        linarith [Real.add_one_le_exp x]
      have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
      rw [Real.exp_add]
      have hmul := mul_le_mul_of_nonneg_left hthree (Real.exp_pos x).le
      linarith [htre z hz, hthi z hz]
    have hlo : x ≤ Real.log ‖T z‖ := by simpa using Real.log_le_log (Real.exp_pos x) hnlo
    have hhi : Real.log ‖T z‖ ≤ x + 2 := by
      simpa using Real.log_le_log (norm_pos_iff.mpr (htne z hz)) hnhi
    rw [mem_ball, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log (T z) - (x : ℂ))
    simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
      Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at h
    dsimp only [comp_apply]
    linarith [Complex.abs_arg_le_pi (T z), Real.pi_lt_four]
  · intro z hz
    have hT : Complex.exp (T z) = z := by
      calc Complex.exp (T z) = Complex.exp (L z) :=
          Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
        _ = z := hinv z hz
    simpa only [comp_apply, expIterate_succ, expIterate_zero,
      Complex.exp_log (htne z hz)] using hT
end ExponentialJuliaSetMisiurewicz

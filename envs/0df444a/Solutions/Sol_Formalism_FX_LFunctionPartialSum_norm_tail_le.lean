-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.norm_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:13.012626+00:00
-- url     : https://prove2.me/submissions/f971c2e5-41ae-40eb-be5b-e3af9e9b035d

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open LFunctionPartialSum
namespace Formalism.FX
namespace LFunctionPartialSum
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact lt_irrefl _ hs
  have K1 : ∀ x : ℝ, 1 ≤ x → ‖(x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hI : Set.uIcc x (x + 1) = Set.Icc x (x + 1) := Set.uIcc_of_le (by linarith)
    have h0 : (0 : ℝ) ∉ Set.uIcc x (x + 1) := by
      rw [hI]
      intro h
      linarith [h.1]
    have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
        HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hr : -s - 1 ≠ -1 := by
        intro h
        apply hs0
        linear_combination -h
      first
      | exact hasDerivAt_ofReal_cpow_const ht0.ne' (neg_ne_zero.mpr hs0)
      | (have h1 := hasDerivAt_ofReal_cpow_const ht0.ne' hr
         have e : -s - 1 + 1 = -s := by ring
         rw [e] at h1
         exact h1)
    have hint : IntervalIntegrable (fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr ht0))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have e2 : (x : ℂ) ^ (-s) - ((x : ℂ) + 1) ^ (-s) =
        -(∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)) := by
      rw [hFTC]
      push_cast
      ring
    have hr' : -s.re - 1 ≠ -1 := by
      intro h
      linarith
    have hgi : IntervalIntegrable (fun t : ℝ => ‖s‖ * t ^ (-s.re - 1)) MeasureTheory.volume x (x + 1) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [hI] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne'))
    rw [e2, norm_neg]
    calc ‖∫ t in x..(x + 1), (-s) * (t : ℂ) ^ (-s - 1)‖
        ≤ ∫ t in x..(x + 1), ‖s‖ * t ^ (-s.re - 1) := by
          refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
            (MeasureTheory.ae_of_all _ (fun t ht => ?_)) hgi
          have ht0 : 0 < t := by linarith [ht.1]
          rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
          simp
      _ = ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hr', h0⟩)]
          have e3 : -s.re - 1 + 1 = -s.re := by ring
          rw [e3]
          have hsr : s.re ≠ 0 := hs.ne'
          field_simp
          ring
  have hterm : ∀ i : ℕ, ‖dterm χ s (i + (N + 1))‖ ≤
      B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    have hx : (1 : ℝ) ≤ ((i + (N + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ i + (N + 1) by omega)
    have h1 := K1 _ hx
    rw [Complex.ofReal_natCast] at h1
    have e : (((i + 1 + (N + 1) : ℕ) : ℝ)) = ((i + (N + 1) : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [e]
    unfold dterm
    rw [norm_mul]
    exact mul_le_mul (hB _) h1 (norm_nonneg _) hB0
  have hf0 : ∀ i : ℕ, 0 ≤ B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    refine mul_nonneg hB0 (mul_nonneg hc (sub_nonneg.mpr ?_))
    have hle : (((i + (N + 1) : ℕ) : ℝ)) ≤ (((i + 1 + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show i + (N + 1) ≤ i + 1 + (N + 1) by omega)
    have hpos : (0 : ℝ) < (((i + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 0 < i + (N + 1) by omega)
    first
    | exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    | exact Real.rpow_le_rpow_of_exponent_nonpos hpos hle (by linarith)
    | (rw [Real.rpow_neg hpos.le, Real.rpow_neg (hpos.le.trans hle)]
       exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hle hs.le))
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub']
    have hv0 : (((0 + (N + 1) : ℕ) : ℝ)) ^ (-s.re) = ((N : ℝ) + 1) ^ (-s.re) := by
      congr 1
      push_cast
      ring
    rw [hv0]
    have hvn : 0 ≤ (((n + (N + 1) : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_nonneg (mul_nonneg hB0 hc) hvn
    nlinarith
  have hsf := summable_of_sum_range_le hf0 hpart
  have hsn : Summable (fun i : ℕ => ‖dterm χ s (i + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsf
  calc ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ ∑' i, ‖dterm χ s (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i : ℕ, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
      first
      | exact Summable.tsum_le_tsum hterm hsn hsf
      | exact tsum_le_tsum hterm hsn hsf
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := Real.tsum_le_of_sum_range_le hf0 hpart
end LFunctionPartialSum
end Formalism.FX

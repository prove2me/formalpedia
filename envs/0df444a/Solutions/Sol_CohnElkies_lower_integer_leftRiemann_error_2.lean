-- Prove2me | solution 2 for CohnElkies.lower_integer_leftRiemann_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:19.694372+00:00
-- url     : https://prove2.me/submissions/8762204f-e17a-4855-bec5-83af32d862c1

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
theorem h47_riemann (f : ℝ → ℝ) (hcont : Continuous f)
    (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → f x ≤ f y) {k : ℕ} (hk : 0 < k) :
    0 ≤ (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hII : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hIc : ∀ c a b : ℝ, IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b :=
    fun c a b => intervalIntegrable_const
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun j : ℕ => (j : ℝ) / (k : ℝ)) (n := k)
    (fun j _ => hII _ _)
  simp only [Nat.cast_zero, zero_div, div_self hk'.ne'] at hsplit
  have hstep : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) / k - (j : ℝ) / k = 1 / k := by
    intro j; push_cast; ring
  have hle : ∀ j : ℕ, (j : ℝ) / k ≤ ((j + 1 : ℕ) : ℝ) / k := by
    intro j
    apply div_le_div_of_nonneg_right _ hk'.le
    push_cast; linarith
  have hlow : ∀ j : ℕ, f ((j : ℝ) / k) ≤ k * ∫ x in (j : ℝ) / k..((j + 1 : ℕ) : ℝ) / k, f x := by
    intro j
    have h := intervalIntegral.integral_mono_on (hle j) (hIc _ _ _) (hII _ _)
      (fun x hx => hmono _ _ (by positivity) hx.1)
    rw [intervalIntegral.integral_const, hstep j, smul_eq_mul] at h
    calc f ((j : ℝ) / k) = k * (1 / k * f ((j : ℝ) / k)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hk'.le
  have hup : ∀ j : ℕ, k * (∫ x in (j : ℝ) / k..((j + 1 : ℕ) : ℝ) / k, f x) ≤
      f (((j + 1 : ℕ) : ℝ) / k) := by
    intro j
    have h := intervalIntegral.integral_mono_on (hle j) (hII _ _) (hIc _ _ _)
      (fun x hx => hmono _ _ (le_trans (by positivity) hx.1) hx.2)
    rw [intervalIntegral.integral_const, hstep j, smul_eq_mul] at h
    calc (k : ℝ) * (∫ x in (j : ℝ) / k..((j + 1 : ℕ) : ℝ) / k, f x)
        ≤ k * (1 / k * f (((j + 1 : ℕ) : ℝ) / k)) := mul_le_mul_of_nonneg_left h hk'.le
      _ = f (((j + 1 : ℕ) : ℝ) / k) := by field_simp
  have hrw : (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) =
      ∑ j ∈ Finset.range k, ((k : ℝ) * (∫ x in (j : ℝ) / k..((j + 1 : ℕ) : ℝ) / k, f x) -
        f ((j : ℝ) / k)) := by
    rw [← hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hrw]
  constructor
  · exact Finset.sum_nonneg fun j _ => by linarith [hlow j]
  · calc ∑ j ∈ Finset.range k, ((k : ℝ) * (∫ x in (j : ℝ) / k..((j + 1 : ℕ) : ℝ) / k, f x) -
          f ((j : ℝ) / k))
        ≤ ∑ j ∈ Finset.range k, (f (((j + 1 : ℕ) : ℝ) / k) - f ((j : ℝ) / k)) :=
          Finset.sum_le_sum fun j _ => by linarith [hup j]
      _ = f 1 - f 0 := by
        rw [Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / k))]
        simp [div_self hk'.ne']

theorem solution
    {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ≤
        lowerRiemannLog T 1 - lowerRiemannLog T 0 := by
  have hsq : ∀ x : ℝ, 0 < Real.sqrt (x ^ 2 + T ^ 2 / 4) := fun x =>
    Real.sqrt_pos.2 (by have : 0 < T ^ 2 := by positivity
                        positivity)
  have hcont : Continuous (lowerRiemannLog T) := by
    unfold lowerRiemannLog
    exact Continuous.log (by fun_prop) (fun x => (hsq x).ne')
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → lowerRiemannLog T x ≤ lowerRiemannLog T y := by
    intro x y hx hxy
    unfold lowerRiemannLog
    exact Real.log_le_log (hsq x) (Real.sqrt_le_sqrt (by nlinarith))
  exact h47_riemann (lowerRiemannLog T) hcont hmono hk


-- Prove2me | solution 2 for CohnElkies.monotone_leftRiemann_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:47.66065+00:00
-- url     : https://prove2.me/submissions/5ef38600-c15f-4816-ba10-63b9ebcfd444

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


theorem solution
    (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hpt : ∀ j : ℕ, j ≤ k → (j:ℝ)/k ∈ Icc (0:ℝ) 1 := fun j hj =>
    ⟨by positivity, by rw [div_le_one hk']; exact_mod_cast hj⟩
  have hle : ∀ j : ℕ, (j:ℝ)/k ≤ ((j+1:ℕ):ℝ)/k := fun j => by gcongr; simp
  have hint : ∀ j : ℕ, j < k → IntervalIntegrable f volume ((j:ℝ)/k) (((j+1:ℕ):ℝ)/k) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    apply hf.mono
    rw [uIcc_of_le (hle j)]
    exact Icc_subset_Icc (hpt j hj.le).1 (hpt (j+1) hj).2
  have hsum : ∑ j ∈ Finset.range k, (∫ x in ((j:ℝ)/k)..(((j+1:ℕ):ℝ)/k), f x) =
      ∫ x in (0:ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j:ℝ)/k)
      (fun j hj => hint j hj)]
    simp [hk'.ne']
  have hlen : ∀ j : ℕ, (((j+1:ℕ):ℝ)/k - (j:ℝ)/k) = 1/k := fun j => by
    push_cast; field_simp; ring
  have hlow : ∀ j ∈ Finset.range k,
      f ((j:ℝ)/k) / k ≤ ∫ x in ((j:ℝ)/k)..(((j+1:ℕ):ℝ)/k), f x := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have := intervalIntegral.integral_mono_on (hle j) intervalIntegrable_const (hint j hj')
      (fun x hx => hf (hpt j hj'.le)
        ⟨(hpt j hj'.le).1.trans hx.1, hx.2.trans (hpt (j+1) hj').2⟩ hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at this
    calc f ((j:ℝ)/k) / k = 1/k * f ((j:ℝ)/k) := by ring
      _ ≤ _ := this
  have hupp : ∀ j ∈ Finset.range k,
      (∫ x in ((j:ℝ)/k)..(((j+1:ℕ):ℝ)/k), f x) ≤ f (((j+1:ℕ):ℝ)/k) / k := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have := intervalIntegral.integral_mono_on (hle j) (hint j hj') intervalIntegrable_const
      (fun x hx => hf
        ⟨(hpt j hj'.le).1.trans hx.1, hx.2.trans (hpt (j+1) hj').2⟩ (hpt (j+1) hj') hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at this
    calc _ ≤ 1/k * f (((j+1:ℕ):ℝ)/k) := this
      _ = _ := by ring
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    have := hlow j hj
    rw [div_le_iff₀ hk'] at this
    nlinarith
  · have htel := Finset.sum_range_sub (fun j : ℕ => f ((j:ℝ)/k)) k
    calc _ ≤ ∑ j ∈ Finset.range k, (f (((j+1:ℕ):ℝ)/k) - f ((j:ℝ)/k)) :=
          Finset.sum_le_sum (fun j hj => by
            have := hupp j hj
            rw [le_div_iff₀ hk'] at this
            linarith)
      _ = f 1 - f 0 := by rw [htel]; simp [hk'.ne']


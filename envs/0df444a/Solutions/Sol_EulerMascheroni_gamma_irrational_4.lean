-- Prove2me | solution 4 for EulerMascheroni.gamma_irrational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T17:46:26.981708+00:00
-- url     : https://prove2.me/submissions/d10f0dc2-5c72-4381-90b1-3f83641e6ac2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Sondow_integral_identity
import Theorems.Thm_EulerMascheroni_Sondow_scaled_integral_bounds_eventually
import Theorems.Thm_EulerMascheroni_Sondow_scaled_A_integral
import Theorems.Thm_EulerMascheroni_Sondow_fractional_lower_bound_conjecture
import Mathlib.Tactic

open EulerMascheroni.Sondow Finset

theorem solution : Irrational Real.eulerMascheroniConstant := by
  intro ⟨r, hr⟩
  obtain ⟨N0, hN0⟩ := scaled_integral_bounds_eventually
  obtain ⟨n, hn, hpos, hfrac⟩ := fractional_lower_bound_conjecture (max r.den N0)
  have hden : r.den ≤ n := le_trans (le_max_left _ _) hn
  have hN : N0 ≤ n := le_trans (le_max_right _ _) hn
  have hd : r.den ∣ d (2*n) := Finset.dvd_lcm (f := id)
    (by simp only [mem_Icc]; exact ⟨r.den_pos, by omega⟩)
  obtain ⟨k, hk⟩ := hd
  obtain ⟨z, hz⟩ := scaled_A_integral n
  have hrat : (d (2*n) : ℝ) * ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant =
      (((k : ℤ) * ((2*n).choose n : ℤ) * r.num : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def, hk]
    push_cast
    field_simp
  have hid := integral_identity n hpos
  push_cast at hrat
  have heq : (d (2*n) : ℝ) * L n = (d (2*n) : ℝ) * I n +
      ((z - (k : ℤ) * ((2*n).choose n : ℤ) * r.num : ℤ) : ℝ) := by
    push_cast
    have hscaled := congrArg (fun t : ℝ => (d (2*n) : ℝ) * t) hid
    nlinarith
  obtain ⟨hlo, hhi⟩ := hN0 n hN hpos
  have hunit : (d (2*n) : ℝ) * I n < 1 :=
    lt_of_lt_of_le hhi (pow_le_one₀ (by norm_num) (by norm_num))
  rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hlo.le, hunit⟩] at hfrac
  exact (not_lt_of_ge hfrac) hhi

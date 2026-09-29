-- Prove2me | solution 3 for EulerMascheroni.gamma_irrational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:09:08.448727+00:00
-- url     : https://prove2.me/submissions/d9951c5a-02f3-471b-a2b7-33a7ce6ec038
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Sondow_integral_identity
import Theorems.Thm_EulerMascheroni_Sondow_scaled_integral_bounds
import Theorems.Thm_EulerMascheroni_Sondow_scaled_A_integral
import Theorems.Thm_EulerMascheroni_Sondow_fractional_lower_bound_conjecture
import Mathlib.Tactic

open EulerMascheroni.Sondow Finset

theorem solution : Irrational Real.eulerMascheroniConstant := by
  intro ⟨r, hr⟩
  obtain ⟨n, hn, hpos, hfrac⟩ := fractional_lower_bound_conjecture r.den
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
  obtain ⟨hlo, hhi⟩ := scaled_integral_bounds n hpos
  have hunit : (d (2*n) : ℝ) * I n < 1 :=
    lt_of_lt_of_le hhi (pow_le_one₀ (by norm_num) (by norm_num))
  rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hlo.le, hunit⟩] at hfrac
  exact (not_lt_of_ge hfrac) hhi

#print axioms solution

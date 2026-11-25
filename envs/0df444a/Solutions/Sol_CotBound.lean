-- Prove2me | solution 1 for CotBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:24:44.160804+00:00
-- url     : https://prove2.me/submissions/f0615f4d-a73e-40fd-ae15-554d826367c7

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_CotBound

set_option autoImplicit false
@[expose] public section
public section
open Real
theorem _root_.solution (m : ℕ) (hm : 2 ≤ m) :
    0 ≤ Real.cos (Real.pi / m) / (Real.sin (Real.pi / m) * m)
      ∧ Real.cos (Real.pi / m) / (Real.sin (Real.pi / m) * m) ≤ 1 / Real.pi := by
  have hm0 : (0:ℝ) < m := by positivity
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hθ0 : 0 < π / m := by positivity
  have hθ2 : π / m ≤ π / 2 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) hmR
  have hc : 0 ≤ Real.cos (π / m) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ2⟩
  have hs : 0 < Real.sin (π / m) := Real.sin_pos_of_pos_of_lt_pi hθ0 (by nlinarith)
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) hpi]
  have hkey : π * Real.cos (π / m) ≤ Real.sin (π / m) * m := by
    rcases eq_or_lt_of_le hθ2 with h | h
    · have : Real.cos (π / m) = 0 := by rw [h]; exact Real.cos_pi_div_two
      rw [this]; simpa using (mul_nonneg hs.le hm0.le)
    · have htan : π / m ≤ Real.tan (π / m) := (Real.lt_tan hθ0 h).le
      rw [Real.tan_eq_sin_div_cos] at htan
      rcases eq_or_lt_of_le hc with hc0 | hc0
      · rw [← hc0]; simpa using (mul_nonneg hs.le hm0.le)
      · rw [le_div_iff₀ hc0] at htan
        have : (π / m) * Real.cos (π / m) * m ≤ Real.sin (π / m) * m :=
          mul_le_mul_of_nonneg_right htan hm0.le
        calc π * Real.cos (π / m) = (π / m) * Real.cos (π / m) * m := by field_simp
          _ ≤ Real.sin (π / m) * m := this
  nlinarith [hkey]

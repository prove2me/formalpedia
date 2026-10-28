-- Prove2me | solution 1 for D1Bound5.two_small_M_window_brackets
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:26:15.215881+00:00
-- url     : https://prove2.me/submissions/0ba13822-f5f9-4eae-be3c-1f9238e02d65

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_ten

section
namespace D1Bound5











theorem twoSmallHeightEnvelope_lt_seven_mul_add_sixty
    (x : ℝ) (hx : 100 ≤ x) : twoSmallHeightEnvelope x < 7*x+60 := by
  have hr : (4047/25 : ℝ)/(x-4) ≤ (4047/25)/96 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hx])
  dsimp [twoSmallHeightEnvelope]
  norm_num at hr
  linarith only [hr]



end D1Bound5
end

section
namespace D1Bound5



theorem _root_.solution
    (C D : ℝ) (hC : (10 : ℝ)^100 ≤ C)
    (hlow : C^7/(10 : ℝ)^50 < D)
    (hhigh : ordinaryLog10 D < twoSmallHeightEnvelope (ordinaryLog10 C))
    (hD : 0 < D) :
    (10 : ℝ)^143*C^5 ≤ D ∧ D ≤ C^11/(10 : ℝ)^87 := by
  have hC0 : 0 < C := by norm_num at hC; linarith only [hC]
  have hC2 : (10 : ℝ)^200 ≤ C^2 := by
    have hh : ((10 : ℝ)^100)^2 ≤ C^2 := by gcongr
    norm_num at hh ⊢
    exact hh
  have hx : 100 ≤ ordinaryLog10 C := by
    have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^100) hC
    simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
  have hlog : ordinaryLog10 D < ordinaryLog10 ((10 : ℝ)^60*C^7) := by
    have hh := hhigh.trans (twoSmallHeightEnvelope_lt_seven_mul_add_sixty (ordinaryLog10 C) hx)
    rw [ordinaryLog10_mul _ _ (by positivity) (by positivity),ordinaryLog10_pow,
      ordinaryLog10_pow,ordinaryLog10_ten]
    norm_num
    linarith only [hh]
  have hupper : D < (10 : ℝ)^60*C^7 := by
    by_contra hbad
    have hh := ordinaryLog10_mono (by positivity : 0 < (10 : ℝ)^60*C^7) (le_of_not_gt hbad)
    linarith only [hlog,hh]
  constructor
  · apply le_of_lt
    apply lt_trans _ hlow
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 10^50)).2
    have hh := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ C^5)
    norm_num at hh ⊢
    nlinarith only [hh,pow_pos hC0 5]
  · apply le_of_lt
    apply lt_trans hupper
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 10^87)).2
    have hC4 : (10 : ℝ)^400 ≤ C^4 := by
      have hh : ((10 : ℝ)^100)^4 ≤ C^4 := by gcongr
      simpa only [← pow_mul] using hh
    have hconst : (10 : ℝ)^147 < 10^400 :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 10) (by decide : 147 < 400)
    calc
      (10 : ℝ)^60*C^7*10^87 = (10 : ℝ)^147*C^7 := by rw [mul_right_comm, ← pow_add]
      _ < (10 : ℝ)^400*C^7 := mul_lt_mul_of_pos_right hconst (pow_pos hC0 7)
      _ ≤ C^4*C^7 := mul_le_mul_of_nonneg_right hC4 (by positivity)
      _ = C^11 := by rw [← pow_add]

end D1Bound5
end

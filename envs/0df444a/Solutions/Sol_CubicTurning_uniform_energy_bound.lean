-- Prove2me | solution 1 for CubicTurning.uniform_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:23:27.29886+00:00
-- url     : https://prove2.me/submissions/26929f3d-ac4b-46c7-af82-9391c17551c3

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









theorem pairEnergy_nonneg (d₀ d₁ : ℂ) : 0 ≤ pairEnergy d₀ d₁ := by
  have h := Complex.re_le_norm (d₀ * conj d₁)
  rw [norm_mul, Complex.norm_conj] at h
  dsimp [pairEnergy]
  linarith

theorem energy_le_pair (e d₀ d₁ : ℂ) : energy e d₀ d₁ ≤ pairEnergy d₀ d₁ := by
  unfold energy
  split_ifs
  · rfl
  · exact pairEnergy_nonneg _ _



theorem strip_count (r x₀ x₁ x₂ y₀ y₁ y₂ : ℝ)
    (hr : 0 ≤ r) (hx : x₀+x₁+x₂=0)
    (hsecond : x₀^2+x₁^2+x₂^2-(y₀^2+y₁^2+y₂^2)=6*r^2)
    (h₀ : |x₀| < r) (h₁ : |x₁| < r) : False := by
  have ha := abs_lt.mp h₀
  have hb := abs_lt.mp h₁
  have hrp : 0 < r := lt_of_le_of_lt (abs_nonneg _) h₀
  have hc : -2*r < x₂ ∧ x₂ < 2*r := by constructor <;> linarith
  have hs₀ : x₀^2 < r^2 := by nlinarith [sq_nonneg (r-x₀), sq_nonneg (r+x₀)]
  have hs₁ : x₁^2 < r^2 := by nlinarith [sq_nonneg (r-x₁), sq_nonneg (r+x₁)]
  have hs₂ : x₂^2 < 4*r^2 := by nlinarith [sq_nonneg (2*r-x₂), sq_nonneg (2*r+x₂)]
  nlinarith [sq_nonneg y₀, sq_nonneg y₁, sq_nonneg y₂]

theorem transverse_budget (y₀ y₁ y₂ : ℝ) (hy : y₀+y₁+y₂=0) :
    y₀^2 ≤ (2/3)*(y₀^2+y₁^2+y₂^2) := by
  have he : y₀ = -y₁-y₂ := by linarith
  rw [he]
  nlinarith [sq_nonneg (y₁-y₂)]











theorem outer_energy_zero (r : ℝ) (hr : 0 ≤ r) (v : ℂ)
    (ho : r ≤ |v.re|) :
    energy (frame r v) (middle r v) (v-middle r v) = 0 := by
  rcases le_or_gt 0 v.re with hx|hx
  · have hout : r ≤ v.re := by simpa [abs_of_nonneg hx] using ho
    simp [frame, hout, middle, hx, energy, halfSlope]
  · have hout : v.re ≤ -r := by rw [abs_of_neg hx] at ho; linarith
    have hnot : ¬r ≤ v.re := by linarith
    simp [frame, hnot, hout, middle, not_le.mpr hx, energy, halfSlope]

theorem inner_pair_bound (r Y : ℝ) (hr : 0 ≤ r) (v : ℂ)
    (hi : |v.re| < r) (hy : v.im^2 ≤ Y) :
    pairEnergy (middle r v) (v-middle r v) ≤
      2*r*(Real.sqrt (r^2+Y)+r) := by
  have hnorm : ‖v-middle r v‖ ≤ Real.sqrt (r^2+Y) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    unfold middle
    split_ifs with hx
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        sub_zero]
      have hxr := (abs_lt.mp hi).2
      nlinarith
    · simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.sub_im,
        Complex.neg_im, Complex.ofReal_im, neg_zero, sub_zero]
      have hxr := (abs_lt.mp hi).1
      have hxn : v.re < 0 := lt_of_not_ge hx
      nlinarith
  have hh : pairEnergy (middle r v) (v-middle r v) =
      2*r*(‖v-middle r v‖ + (r-|v.re|)) := by
    unfold pairEnergy middle
    split_ifs with hx
    · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hx]
      ring
    · simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Real.norm_eq_abs, abs_of_nonneg hr, abs_of_neg (lt_of_not_ge hx)]
      ring
  rw [hh]
  have hxr : 0 ≤ |v.re| := abs_nonneg _
  nlinarith














































































end CubicTurning

open CubicTurning in
theorem solution (r : ℝ) (a b c : ℂ) (hr : 0 ≤ r)
    (hcenter : a+b+c=0)
    (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    let Y := (2/3)*(a.im^2+b.im^2+c.im^2)
    (endpointEnergy r a+endpointEnergy r b+endpointEnergy r c)/3 ≤
      (2*r*(Real.sqrt (r^2+Y)+r))/3 := by
  dsimp only
  let Y := (2/3)*(a.im^2+b.im^2+c.im^2)
  let B := 2*r*(Real.sqrt (r^2+Y)+r)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hx : a.re+b.re+c.re=0 := by
    have h := congrArg Complex.re hcenter
    simpa using h
  have hy : a.im+b.im+c.im=0 := by
    have h := congrArg Complex.im hcenter
    simpa using h
  have hs : a.re^2+b.re^2+c.re^2-(a.im^2+b.im^2+c.im^2)=6*r^2 := by
    have h := congrArg Complex.re hsecond
    simp [pow_two, Complex.mul_re] at h
    nlinarith
  have ha : a.im^2 ≤ Y := transverse_budget _ _ _ hy
  have hb : b.im^2 ≤ Y := by dsimp [Y]; nlinarith [transverse_budget b.im a.im c.im (by linarith)]
  have hc : c.im^2 ≤ Y := by dsimp [Y]; nlinarith [transverse_budget c.im a.im b.im (by linarith)]
  have hout (v : ℂ) (hv : ¬|v.re| < r) : endpointEnergy r v=0 :=
    outer_energy_zero r hr v (le_of_not_gt hv)
  have hin (v : ℂ) (hv : |v.re| < r) (hyv : v.im^2 ≤ Y) : endpointEnergy r v ≤ B :=
    (energy_le_pair _ _ _).trans (inner_pair_bound _ _ hr _ hv hyv)
  by_cases hia : |a.re| < r
  · have hib : ¬|b.re| < r := fun h => strip_count r _ _ _ _ _ _ hr hx hs hia h
    have hic : ¬|c.re| < r := by
      intro h
      exact strip_count r a.re c.re b.re a.im c.im b.im hr (by linarith) (by nlinarith) hia h
    rw [hout b hib,hout c hic]
    have h := hin a hia ha
    dsimp [B,Y] at h
    linarith
  · rw [hout a hia]
    by_cases hib : |b.re| < r
    · have hic : ¬|c.re| < r := by
        intro h
        exact strip_count r b.re c.re a.re b.im c.im a.im hr (by linarith) (by nlinarith) hib h
      rw [hout c hic]
      have h := hin b hib hb
      dsimp [B,Y] at h
      linarith
    · rw [hout b hib]
      by_cases hic : |c.re| < r
      · have h := hin c hic hc
        dsimp [B,Y] at h
        linarith
      · rw [hout c hic]
        dsimp [B,Y] at hB
        linarith

-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_45
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T15:35:43.569436+00:00
-- url     : https://prove2.me/submissions/81e373a2-aaf3-498e-b5a2-eab2269c2719

import Mathlib

import Definitions.Def_GaussLocalMaxColoring_Main_Section5

set_option autoImplicit false

set_option maxHeartbeats 1500000

section


set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def improvedNu : ℝ := 437/2000

def improvedPsi (s : ℝ) : ℝ :=
  if s ≤ improvedNu then Real.sqrt 3*Real.sqrt (1-s^2)
  else Real.sqrt 3*(1-improvedNu*s)/Real.sqrt (1-improvedNu^2)

theorem improved_nu_pos : 0 < improvedNu := by norm_num [improvedNu]
theorem improved_nu_lt_one : improvedNu < 1 := by norm_num [improvedNu]

theorem improved_drift (U : ℝ) (hU0 : 0 ≤ U) (hUH : U ≤ Real.sqrt H5) :
    U/2+1/1500 ≤ Real.sqrt 3/2*improvedPsi (Real.sqrt (H5-U^2)) := by
  have hH : 0 ≤ H5 := by norm_num [H5,H0,beta5,eta5]
  have hHsmall : H5 < (13/5:ℝ)^2 := by norm_num [H5,H0,beta5,eta5]
  have hHU : U ≤ 13/5 := hUH.trans (Real.sqrt_le_iff.mpr ⟨by norm_num,hHsmall.le⟩)
  have hU2 : U^2 ≤ H5 := by
    have hm := pow_le_pow_left₀ hU0 hUH 2
    rwa [Real.sq_sqrt hH] at hm
  let s : ℝ := Real.sqrt (H5-U^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=H5-U^2 := Real.sq_sqrt (sub_nonneg.mpr hU2)
  have hrt3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  change U/2+1/1500 ≤ Real.sqrt 3/2*improvedPsi s
  unfold improvedPsi
  split
  · rename_i hsν
    have hprod := mul_nonneg (sub_nonneg.mpr hsν) (add_nonneg improved_nu_pos.le hs0)
    have hrad : (9/10:ℝ)^2 ≤ 1-s^2 := by
      have hν2 : improvedNu^2 < (1/10:ℝ) := by norm_num [improvedNu]
      nlinarith only [hprod,hν2]
    have hr := Real.le_sqrt_of_sq_le hrad
    have hmul : Real.sqrt 3/2*(Real.sqrt 3*Real.sqrt (1-s^2))=3/2*Real.sqrt (1-s^2) := by
      nlinarith only [congrArg (fun x : ℝ => x*Real.sqrt (1-s^2)) hrt3]
    rw [hmul]
    linarith only [hr,hHU]
  · rename_i hsν
    let a : ℝ := Real.sqrt (1-improvedNu^2)
    have haRad : 0 < 1-improvedNu^2 := by norm_num [improvedNu]
    have ha : 0 < a := Real.sqrt_pos.mpr haRad
    have ha2 : a^2=1-improvedNu^2 := Real.sq_sqrt haRad.le
    have ha1 : a ≤ 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num,by have h := sq_nonneg improvedNu; linarith only [h]⟩
    have hCS : (a*U+3*improvedNu*s)^2 ≤ (1+8*improvedNu^2)*H5 := by
      have hh := sq_nonneg (a*s-3*improvedNu*U)
      have hid : (a*U+3*improvedNu*s)^2+(a*s-3*improvedNu*U)^2=
          (a^2+9*improvedNu^2)*(U^2+s^2) := by ring
      rw [ha2,show U^2+s^2=H5 by linarith only [hs2]] at hid
      nlinarith only [hh,hid]
    have hNum : (1+8*improvedNu^2)*H5 ≤ (3-1/750:ℝ)^2 := by
      norm_num [improvedNu,H5,H0,beta5,eta5]
    have hupper : a*U+3*improvedNu*s ≤ 3-1/750 := by
      nlinarith only [hCS,hNum]
    have htarget : (U+1/750)*a ≤ 3*(1-improvedNu*s) := by
      nlinarith only [hupper,ha1]
    have hid : Real.sqrt 3/2*(Real.sqrt 3*(1-improvedNu*s)/a)=3*(1-improvedNu*s)/(2*a) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) ha.ne')).mpr
      calc
        Real.sqrt 3/2*(Real.sqrt 3*(1-improvedNu*s)/a)*(2*a) =
            (Real.sqrt 3)^2*(1-improvedNu*s)*(a/a) := by ring
        _ = 3*(1-improvedNu*s) := by rw [div_self ha.ne',mul_one,hrt3]
    rw [hid]
    apply (le_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    nlinarith only [htarget]

end
end GaussLocalMaxColoring.Main


end

section


set_option autoImplicit false

namespace GaussLocalMaxColoring.Main

/-- Lemma 45 of the fixed STOC paper, with its auxiliary function expanded locally. -/
theorem lemma_45 (U : ℝ) (hU0 : 0 ≤ U) (hUH : U ≤ Real.sqrt H5) :
    let ν : ℝ := 437 / 2000
    let ψ : ℝ → ℝ := fun s =>
      if s ≤ ν then Real.sqrt 3 * Real.sqrt (1-s^2)
      else Real.sqrt 3 * (1-ν*s) / Real.sqrt (1-ν^2)
    U / 2 + 1 / 1500 ≤ Real.sqrt 3 / 2 * ψ (Real.sqrt (H5-U^2)) := by
  exact improved_drift U hU0 hUH

end GaussLocalMaxColoring.Main


end

open GaussLocalMaxColoring.Main

theorem solution (U : ℝ) (hU0 : 0 ≤ U) (hUH : U ≤ Real.sqrt H5) :
    let ν : ℝ := 437 / 2000
    let ψ : ℝ → ℝ := fun s =>
      if s ≤ ν then Real.sqrt 3 * Real.sqrt (1-s^2)
      else Real.sqrt 3 * (1-ν*s) / Real.sqrt (1-ν^2)
    U / 2 + 1 / 1500 ≤ Real.sqrt 3 / 2 * ψ (Real.sqrt (H5-U^2)) := by
  exact GaussLocalMaxColoring.Main.lemma_45 U hU0 hUH

#print axioms solution

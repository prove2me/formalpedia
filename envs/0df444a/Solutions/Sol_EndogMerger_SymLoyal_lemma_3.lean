-- Prove2me | solution 1 for EndogMerger.SymLoyal.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:46:52.732327+00:00
-- url     : https://prove2.me/submissions/96635ecf-b85b-4488-9db5-72872c4d75dc

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions
set_option autoImplicit false
noncomputable section
open EndogMerger.SymLoyal Set

private lemma cubic_sign (b a : ℝ) (hb : 0 < b ∧ b < 1/3 ∧ cubic0 b=0)
    (ha : 0 < a) (ha3 : a < 1/3) : 0 < cubic0 a ↔ a < b := by
  have hb7 : b < 1/7 := by
    by_contra hn
    have hge : 1/7 ≤ b := le_of_not_gt hn
    let T := -43*(b^2+b/7+(1/7:ℝ)^2)+43*(b+1/7)-13
    have hT : T < 0 := by
      have hp := mul_pos (sub_pos.mpr hb.2.1) (by linarith : 0 < 1-b-1/3-1/7)
      dsimp [T]
      nlinarith
    have hc : cubic0 b = cubic0 (1/7)+(b-1/7)*T := by dsimp [cubic0,T];ring
    have hv : cubic0 (1/7) < 0 := by norm_num [cubic0]
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hge) hT.le
    linarith [hb.2.2]
  let B := 43*(a^2+a*b+b^2)-43*(a+b)+13
  have hB : 0 < B := by
    have hp := mul_pos (sub_pos.mpr ha3) (by linarith : 0 < 2/3-a-b)
    have hq := mul_pos (sub_pos.mpr hb7) (by linarith : 0 < 2/3-b-1/7)
    dsimp [B]
    nlinarith
  have hc : cubic0 a=(b-a)*B := by
    have he : cubic0 a-cubic0 b=(b-a)*B := by dsimp [cubic0,B];ring
    rw [hb.2.2,sub_zero] at he
    exact he
  rw [hc,mul_pos_iff_of_pos_right hB,sub_pos]

private lemma q0_positive (b a k : ℝ) (hb : 0 < b ∧ b < 1/3 ∧ cubic0 b=0)
    (ha : 0 < a) (ha3 : a < 1/3) :
    0 < -(1-3*a)*(2-5*a)*k^2+(1-a)*(1-3*a)*(1-2*a)*k-a*(1-2*a)^3 ↔ Omega0₁ b a k := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hd : 0 < 2-5*a := by linarith
  let A := (1-3*a)*(2-5*a)
  let M := (1-a)*(1-3*a)*(1-2*a)
  let D := (1-3*a)*cubic0 a
  let Q := -A*k^2+M*k-a*(1-2*a)^3
  have hid : 4*A*Q=(1-2*a)^2*D-(2*A*k-M)^2 := by dsimp [A,Q,M,D,cubic0];ring
  have hA : 0 < A := mul_pos hz hd
  constructor
  · intro H
    have H0 := H
    have H : 0 < Q := by dsimp [Q,A,M];nlinarith only [H0]
    have hD : 0 < D := by
      have hp := mul_pos (by dsimp [A];positivity : 0 < 4*A) H
      have hsq := sq_nonneg (2*A*k-M)
      have hh : 0 < (1-2*a)^2*D := by linarith
      exact (mul_pos_iff_of_pos_left (pow_pos hx 2)).mp hh
    have hc : 0 < cubic0 a := (mul_pos_iff_of_pos_left hz).mp hD
    have hab := (cubic_sign b a hb ha ha3).mp hc
    have hs := Real.sq_sqrt hD.le
    have hscaled : ((1-2*a)*Real.sqrt D)^2=(1-2*a)^2*D := by rw [mul_pow,hs]
    have hsp := Real.sqrt_nonneg D
    have hp := mul_pos (by dsimp [A];positivity : 0 < 4*A) H
    have hsq : (2*A*k-M)^2 < ((1-2*a)*Real.sqrt D)^2 := by
      rw [hscaled]
      linarith only [hid,hp]
    have bounds := abs_lt_of_sq_lt_sq' hsq (mul_nonneg hx.le hsp)
    have hlo := bounds.1
    have hhi := bounds.2
    refine ⟨ha,hab,?_,?_⟩
    · apply (div_lt_iff₀ (by positivity : 0 < 2*(1-3*a)*(2-5*a))).mpr
      dsimp [M,A,D] at hlo
      nlinarith only [hlo]
    · apply (lt_div_iff₀ (by positivity : 0 < 2*(1-3*a)*(2-5*a))).mpr
      dsimp [M,A,D] at hhi
      nlinarith only [hhi]
  · rintro ⟨_,hab,hlo,hhi⟩
    have hc := (cubic_sign b a hb ha ha3).mpr hab
    have hD : 0 < D := mul_pos hz hc
    have hs := Real.sq_sqrt hD.le
    have hscaled : ((1-2*a)*Real.sqrt D)^2=(1-2*a)^2*D := by rw [mul_pow,hs]
    have hlo' := (div_lt_iff₀ (by positivity : 0 < 2*(1-3*a)*(2-5*a))).mp hlo
    have hhi' := (lt_div_iff₀ (by positivity : 0 < 2*(1-3*a)*(2-5*a))).mp hhi
    have hl : 0 < (1-2*a)*Real.sqrt D+(2*A*k-M) := by dsimp [D,A,M];nlinarith only [hlo',hhi']
    have hh : 0 < (1-2*a)*Real.sqrt D-(2*A*k-M) := by dsimp [D,A,M];nlinarith only [hlo',hhi']
    have hsq := sq_lt_sq' (by linarith only [hl] : -((1-2*a)*Real.sqrt D) < 2*A*k-M) (by linarith only [hh] : 2*A*k-M < (1-2*a)*Real.sqrt D)
    rw [hscaled] at hsq
    have he : 0 < 4*A*Q := by linarith only [hid,hsq]
    have hh := (mul_pos_iff_of_pos_left (by positivity : 0 < 4*A)).mp he
    dsimp [Q,A,M] at hh
    nlinarith only [hh]

private lemma q0_active_cut (b a k : ℝ) (hb : 0 < b ∧ b < 1/3 ∧ cubic0 b=0)
    (ha : 0 < a) (ha3 : a < 1/3) (H : Omega0₁ b a k) : k < kCut a := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hd : 0 < 2-5*a := by linarith
  let A := (1-3*a)*(2-5*a)
  let M := (1-a)*(1-3*a)*(1-2*a)
  let Q := fun t : ℝ => -A*t^2+M*t-a*(1-2*a)^3
  have hQ : 0 < Q k := by
    have hh := (q0_positive b a k hb ha ha3).mpr H
    dsimp [Q,A,M]
    nlinarith only [hh]
  have hQc : Q (kCut a)=-a*(1-2*a)^4/(2-5*a) := by
    dsimp [Q,A,M,kCut]
    field_simp [hd.ne']
    ring_nf
    have hn : 2-a*5 ≠ 0 := by linarith
    have hnn : 4-a*20+a^2*25 ≠ 0 := by nlinarith [sq_pos_of_pos hd]
    field_simp [hn,hnn]
    ring
  have hQcn : Q (kCut a) < 0 := by
    rw [hQc]
    exact div_neg_of_neg_of_pos (by have hh:=mul_pos ha (pow_pos hx 4);nlinarith) hd
  have hder : M-2*A*kCut a=-(1-2*a)*(1-3*a)^2 := by
    dsimp [M,A,kCut]
    field_simp [hd.ne']
    ring_nf
    have hn : 2-a*5 ≠ 0 := by linarith
    field_simp [hn]
    ring
  have hdn : M-2*A*kCut a < 0 := by rw [hder];have hh:=mul_pos hx (pow_pos hz 2);nlinarith
  by_contra hn
  have hge := le_of_not_gt hn
  have hid : Q k=Q (kCut a)+(k-kCut a)*(M-2*A*kCut a)-A*(k-kCut a)^2 := by dsimp [Q];ring
  have hn1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hge) hdn.le
  have hn2 := mul_nonneg (mul_pos hz hd).le (sq_nonneg (k-kCut a))
  change 0 ≤ A*(k-kCut a)^2 at hn2
  linarith

private lemma q0_gap (a k r : ℝ) (hx : 1-2*a ≠ 0) (hk : k ≠ 0) (hden : a+s1 a k ≠ 0) :
    r*(a+s2 a k)/(1-2*a)-r*a/k =
      r*(1-2*a-k)*(-(1-3*a)*(2-5*a)*k^2+(1-a)*(1-3*a)*(1-2*a)*k-a*(1-2*a)^3)/
      ((a+s1 a k)*(1-2*a)^3*k) := by
  unfold s2
  field_simp [hx,hk,hden]
  unfold s1
  field_simp [hx]
  ring_nf
  have hn : 1-a*2 ≠ 0 := by intro hh;apply hx;linarith
  have hnn : 1-a*6+a^2*12-a^3*8 ≠ 0 := by
    have he : 1-a*6+a^2*12-a^3*8=(1-2*a)^3 := by ring
    rw [he]
    exact pow_ne_zero 3 hx
  field_simp [hn,hnn]
  ring

private lemma independent_regions (b a k r : ℝ) (hb : 0 < b ∧ b < 1/3 ∧ cubic0 b=0)
    (ha : 0 < a) (ha3 : a < 1/3) (hak : a < k) (hk : k < 1-2*a) (hr : 0 < r) :
    (Omega0₁ b a k → L0 a k r=r*(a+s2 a k)/(1-2*a) ∧ piIndepA a k r=r*(a+s2 a k) ∧ piIndepB a k r=r*(a+s2 a k)*k/(1-2*a)) ∧
    (Omega0₂ b a k → L0 a k r=r*a/k ∧ piIndepA a k r=r*a*(1-2*a)/k ∧ piIndepB a k r=r*a) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hs : 0 < s1 a k := by
    unfold s1
    apply mul_pos hz
    have hh := (div_lt_one hx).mpr hk
    linarith
  have hden : 0 < a+s1 a k := add_pos ha hs
  constructor
  · intro H
    have hc := q0_active_cut b a k hb ha ha3 H
    have hQ := (q0_positive b a k hb ha ha3).mpr H
    have hX : r*a/k < r*(a+s2 a k)/(1-2*a) := by
      have hh : 0 < r*(a+s2 a k)/(1-2*a)-r*a/k := by
        rw [q0_gap a k r hx.ne' hkp.ne' hden.ne']
        exact div_pos (mul_pos (mul_pos hr (sub_pos.mpr hk)) hQ) (mul_pos (mul_pos hden (pow_pos hx 3)) hkp)
      linarith
    simp only [L0,piIndepA,piIndepB,if_pos hc,max_eq_left hX.le]
    refine ⟨trivial,?_,?_⟩ <;> field_simp [hx.ne'] <;> ring
  · intro H
    have hQ : -(1-3*a)*(2-5*a)*k^2+(1-a)*(1-3*a)*(1-2*a)*k-a*(1-2*a)^3 ≤ 0 := by
      by_contra hn
      exact H.1 ((q0_positive b a k hb ha ha3).mp (lt_of_not_ge hn))
    have hX : r*(a+s2 a k)/(1-2*a) ≤ r*a/k := by
      have hh : r*(a+s2 a k)/(1-2*a)-r*a/k ≤ 0 := by
        rw [q0_gap a k r hx.ne' hkp.ne' hden.ne']
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (mul_pos hr (sub_pos.mpr hk)).le hQ) (mul_pos (mul_pos hden (pow_pos hx 3)) hkp).le
      linarith
    by_cases hc : k < kCut a
    · simp only [L0,piIndepA,piIndepB,if_pos hc,max_eq_right hX]
      refine ⟨trivial,?_,?_⟩ <;> field_simp [hkp.ne'] <;> ring
    · simp only [L0,piIndepA,piIndepB,if_neg hc,if_pos hk]
      exact ⟨trivial,trivial,trivial⟩
theorem solution (α₁ : ℝ) (hα₁ : 0 < α₁ ∧ α₁ < 1 / 3 ∧ cubic0 α₁ = 0)
    (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (Omega0₁ α₁ α k →
      L0 α k r = r * (α + s2 α k) / (1 - 2 * α) ∧
      piIndepA α k r = r * (α + s2 α k) ∧
      piIndepB α k r = r * (α + s2 α k) * k / (1 - 2 * α)) ∧
    (Omega0₂ α₁ α k →
      L0 α k r = r * α / k ∧
      piIndepA α k r = r * α * (1 - 2 * α) / k ∧
      piIndepB α k r = r * α) := by
  exact independent_regions α₁ α k r hα₁ hα0 hα3 hαk hk hr

#print axioms solution

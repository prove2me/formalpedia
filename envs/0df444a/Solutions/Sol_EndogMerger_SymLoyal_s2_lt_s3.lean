-- Prove2me | solution 1 for EndogMerger.SymLoyal.s2_lt_s3
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:30:58.331272+00:00
-- url     : https://prove2.me/submissions/81f4d191-d2a6-4daa-9e96-e507c9a50182

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions
set_option autoImplicit false
noncomputable section
open EndogMerger.SymLoyal Set

private lemma cut_lt (a : ℝ) (ha : 0 < a) (hb : a < 1/3) : kCut a < 1-2*a := by
  unfold kCut
  rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
  nlinarith [mul_pos (by linarith : 0 < 1-2*a) (by linarith : 0 < 1-3*a)]

private lemma high_capacity (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hk : 1-2*a ≤ k) :
    {S | IsEquilibriumStructure a k r S} = {MarketStructure.indep} := by
  have hn : ¬ k < 1-2*a := not_lt.mpr hk
  have hc : ¬ k < kCut a := not_lt.mpr ((cut_lt a ha hb).le.trans hk)
  have hm : ¬ k < (1-a)/2 := by linarith
  have h1 : ¬ cond1a a k r := by
    simp only [cond1a, piAB, piIndepA, piIndepB, hc, hn, hm, ite_false]
    nlinarith
  have h2 : ¬ cond2a a k r := by
    simp only [cond2a, piIndepB, piBCB, piBC, hc, hn, hm, ite_false]
    nlinarith
  ext S
  cases S <;> simp [IsEquilibriumStructure, h1, h2]

private lemma s_difference (a k : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k) (hk : k < kCut a) :
    s2 a k < s3 a k := by
  have hd : 0 < 2-5*a := by linarith
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkx : k < 1-2*a := hk.trans (cut_lt a ha hb)
  have hkp : 0 < k := ha.trans hak
  have hs : 0 < s1 a k := by
    unfold s1
    apply mul_pos hz
    have hh : k/(1-2*a) < 1 := (div_lt_one hx).mpr hkx
    linarith
  have hden : 0 < a+s1 a k := add_pos ha hs
  have hcut : k*(2-5*a) < (1-2*a)^2 := (lt_div_iff₀ hd).mp hk
  let Q := 2*(1-2*a)^2-k*(3-7*a)
  have hQd : 0 < Q*(2-5*a) := by
    have hh := mul_lt_mul_of_pos_left hcut (by linarith : 0 < 3-7*a)
    have hp := mul_pos (pow_pos hx 2) hz
    dsimp [Q]
    nlinarith
  have hQ : 0 < Q := by
    by_contra hh
    have hnp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hd.le
    linarith
  have he : s3 a k-s2 a k = a*k*(1-3*a)*Q/((1-a)*(1-2*a)^2*(a+s1 a k)) := by
    unfold s2 s3
    field_simp [hx.ne', h1.ne', hden.ne']
    unfold s1 Q
    field_simp [hx.ne']
    ring_nf
    have hn : 1-a*2 ≠ 0 := by linarith
    have hnn : 1-a*4+a^2*4 ≠ 0 := by nlinarith [sq_pos_of_pos hx]
    field_simp [hn, hnn]
    ring
  have hp : 0 < s3 a k-s2 a k := by
    rw [he]
    exact div_pos (mul_pos (mul_pos (mul_pos ha hkp) hz) hQ)
      (mul_pos (mul_pos h1 (pow_pos hx 2)) hden)
  linarith

private lemma sigma_ineq (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < kCut a) (hr : 0 < r) :
    r*(1-2*a+k)*(a+s2 a k)/(1-2*a) < r*(2*a+s1 a k) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hd : 0 < 2-5*a := by linarith
  have he : 0 < 3-8*a := by linarith
  have hkx := hk.trans (cut_lt a ha hb)
  have hs : 0 < s1 a k := by
    unfold s1
    apply mul_pos hz
    have hh := (div_lt_one hx).mpr hkx
    linarith
  have hden : 0 < a+s1 a k := add_pos ha hs
  let R := (1-3*a)*(2-5*a)*(k-a)^2 + a*(1-3*a)*(3-8*a)*(k-a) +
    a*(a^3+(1-3*a)*(1-2*a))
  have hR : 0 < R := by
    have h1 := mul_nonneg (mul_nonneg hz.le hd.le) (sq_nonneg (k-a))
    have h2 := mul_nonneg (mul_nonneg (mul_nonneg ha.le hz.le) he.le) (sub_nonneg.mpr hak.le)
    have h3 := mul_pos ha (add_pos (pow_pos ha 3) (mul_pos hz hx))
    dsimp [R]
    linarith
  have hidentity : (2*a+s1 a k)-(1-2*a+k)*(a+s2 a k)/(1-2*a) =
      (1-2*a-k)*R/((1-2*a)^3*(a+s1 a k)) := by
    unfold s2
    field_simp [hx.ne', hden.ne']
    unfold s1 R
    field_simp [hx.ne']
    ring
  have hg : 0 < (2*a+s1 a k)-(1-2*a+k)*(a+s2 a k)/(1-2*a) := by
    rw [hidentity]
    exact div_pos (mul_pos (sub_pos.mpr hkx) hR) (mul_pos (pow_pos hx 3) hden)
  have hm := mul_lt_mul_of_pos_left (sub_pos.mp hg) hr
  simpa [mul_div_assoc, mul_assoc] using hm

private lemma supports (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k) (hr : 0 < r) :
    L0 a k r ≤ LBC a k r ∧ LBC a k r ≤ LAB a k r := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hcm : kCut a < (1-a)/2 := by
    unfold kCut
    rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
    nlinarith [mul_pos ha hz]
  have hmx : (1-a)/2 < 1-2*a := by linarith
  by_cases hc : k < kCut a
  · have hm : k < (1-a)/2 := hc.trans hcm
    have hkx : k < 1-2*a := hm.trans hmx
    have h23 := s_difference a k ha hb hak hc
    have hXY : r*(a+s2 a k)/(1-2*a) ≤ r*(a+s3 a k)/(1-2*a) :=
      (div_le_div_iff_of_pos_right hx).mpr (mul_le_mul_of_nonneg_left (by linarith) hr.le)
    have hYU : r*(a+s3 a k)/(1-2*a) ≤ r*(2*a+s1 a k)/(1-a) := by
      have hi : r*(2*a+s1 a k)/(1-a)-r*(a+s3 a k)/(1-2*a) =
          r*k*(1-3*a)/((1-a)*(1-2*a)) := by
        unfold s1 s3
        field_simp [hx.ne',h1.ne']
        ring
      have hp : 0 ≤ r*(2*a+s1 a k)/(1-a)-r*(a+s3 a k)/(1-2*a) := by
        rw [hi]
        positivity
      linarith
    simpa only [L0,LBC,LAB,if_pos hc,if_pos hm] using
      And.intro (max_le_max hXY (le_refl (r*a/k))) (max_le_max hYU (le_refl (r*a/k)))
  · by_cases hm : k < (1-a)/2
    · have hkx : k < 1-2*a := hm.trans hmx
      simp only [L0,LBC,LAB,if_neg hc,if_pos hm,if_pos hkx]
      exact ⟨le_refl _,le_max_right _ _⟩
    · have hm' : (1-a)/2 ≤ k := le_of_not_gt hm
      have hVL : r*a/k ≤ 2*r*a/(1-a) := by
        apply (div_le_div_iff₀ hkp h1).mpr
        have hp := mul_nonneg (mul_nonneg hr.le ha.le) (by linarith : 0 ≤ 2*k-(1-a))
        nlinarith
      by_cases hkx : k < 1-2*a
      · have hs : 0 ≤ s1 a k := by
          unfold s1
          apply mul_nonneg hz.le
          have hh := (div_lt_one hx).mpr hkx
          linarith
        have hLU : 2*r*a/(1-a) ≤ r*(2*a+s1 a k)/(1-a) := by
          apply (div_le_div_iff_of_pos_right h1).mpr
          nlinarith [mul_nonneg hr.le hs]
        simpa only [L0,LBC,LAB,if_neg hc,if_neg hm,if_pos hkx] using And.intro hVL hLU
      · have hVL' : r*a/(1-2*a) ≤ 2*r*a/(1-a) := by
          apply (div_le_div_iff₀ hx h1).mpr
          have hp := mul_nonneg (mul_nonneg hr.le ha.le) hz.le
          nlinarith
        simpa only [L0,LBC,LAB,if_neg hc,if_neg hm,if_neg hkx] using And.intro hVL' (le_refl (2*r*a/(1-a)))
theorem solution (α k : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < kCut α) :
    s2 α k < s3 α k := by
  exact s_difference α k hα0 hα3 hαk hk

#print axioms solution

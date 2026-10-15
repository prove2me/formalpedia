-- Prove2me | solution 1 for EndogMerger.SymLoyal.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:44:11.957089+00:00
-- url     : https://prove2.me/submissions/b9544a40-ed95-4271-95a1-52a635b8c24c

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

private lemma threshold (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (k < kStar a → piAB a k r < piIndepA a k r+piIndepB a k r) ∧
    (kStar a < k → piIndepA a k r+piIndepB a k r < piAB a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkp : 0 < k := ha.trans hak
  let A := r*(2*a+s1 a k)
  let B := (1-a)*(r*a/k)
  let C := r*(1-2*a+k)*(a+s2 a k)/(1-2*a)
  let D := r*a*(1-2*a+k)/k
  have hBD : B < D := by
    dsimp [B,D]
    apply (lt_div_iff₀ hkp).mpr
    have hc : (r*a/k)*k = r*a := div_mul_cancel₀ _ hkp.ne'
    have hp := mul_pos (mul_pos hr ha) (sub_pos.mpr hak)
    nlinarith
  have hid : A-D = r*(1-2*a-k)*((1-3*a)*k-a*(1-2*a))/((1-2*a)*k) := by
    dsimp [A,D,s1]
    field_simp [hx.ne',hkp.ne']
    ring
  have hsign : (k < kStar a → A < D) ∧ (kStar a < k → D < A) := by
    constructor
    · intro hh
      have hq : (1-3*a)*k-a*(1-2*a) < 0 := by
        have hh' := (lt_div_iff₀ hz).mp hh
        nlinarith
      have hh' : A-D < 0 := by
        rw [hid]
        exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hr (sub_pos.mpr hk)) hq) (mul_pos hx hkp)
      linarith
    · intro hh
      have hq : 0 < (1-3*a)*k-a*(1-2*a) := by
        have hh' := (div_lt_iff₀ hz).mp hh
        nlinarith
      have hh' : 0 < A-D := by
        rw [hid]
        exact div_pos (mul_pos (mul_pos hr (sub_pos.mpr hk)) hq) (mul_pos hx hkp)
      linarith
  have hab : piAB a k r = if k < (1-a)/2 then max A B else A := by
    by_cases hm : k < (1-a)/2
    · simp only [piAB,LAB,if_pos hm]
      rw [mul_max_of_nonneg _ _ h1.le]
      dsimp [A,B]
      congr 1
      field_simp [h1.ne']
    · simp only [piAB,if_neg hm,if_pos hk,if_false]
      rfl
  by_cases hc : k < kCut a
  · have hi : piIndepA a k r+piIndepB a k r = max C D := by
      simp only [piIndepA,piIndepB,L0,if_pos hc]
      rw [← add_mul, mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1-2*a+k)]
      dsimp [C,D]
      congr 1 <;> ring
    have hCA : C < A := sigma_ineq a k r ha hb hak hc hr
    rw [hi,hab]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      split_ifs
      · exact (max_lt hAD hBD).trans_le (le_max_right C D)
      · exact hAD.trans_le (le_max_right C D)
    · intro hh
      have hDA := hsign.2 hh
      have hiA : max C D < A := max_lt hCA hDA
      split_ifs
      · exact hiA.trans_le (le_max_left A B)
      · exact hiA
  · have hi : piIndepA a k r+piIndepB a k r = D := by
      simp only [piIndepA,piIndepB,if_neg hc,if_pos hk]
      dsimp [D]
      field_simp [hkp.ne']
    rw [hi,hab]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      split_ifs
      · exact max_lt hAD hBD
      · exact hAD
    · intro hh
      have hDA := hsign.2 hh
      split_ifs
      · exact hDA.trans_le (le_max_left A B)
      · exact hDA

private lemma remaining_C (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) : piBCB a k r ≤ piABC a k r := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hcm : kCut a < (1-a)/2 := by
    unfold kCut
    rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
    nlinarith [mul_pos ha hz]
  by_cases hm : k < (1-a)/2
  · have H := (supports a k r ha hb hak hr).2
    by_cases hc : k < kCut a
    · simp only [LBC,LAB,if_pos hc,if_pos hm] at H
      simp only [piBCB,piBC,piABC,LBC,LAB,if_pos hc,if_pos hm]
      have hi : 2*k*max (r*(a+s3 a k)/(1-2*a)) (r*a/k)/2 = k*max (r*(a+s3 a k)/(1-2*a)) (r*a/k) := by ring
      rw [hi]
      exact mul_le_mul_of_nonneg_left H hkp.le
    · have H' : r*a/k ≤ LAB a k r := by simpa only [LBC,if_neg hc,if_pos hm] using H
      have HH := mul_le_mul_of_nonneg_left H' hkp.le
      have hi : k*(r*a/k)=r*a := by field_simp [hkp.ne']
      rw [hi] at HH
      simpa only [piBCB,piBC,piABC,if_neg hc,if_pos hm,show 2*r*a/2=r*a by ring] using HH
  · have hm' : (1-a)/2 ≤ k := le_of_not_gt hm
    have hc : ¬ k < kCut a := by linarith
    let F := fun t : ℝ => (1-a)*(1-2*a)*(t-a)-(1-3*a)*t^2
    have hFm : 0 < F ((1-a)/2) := by
      have heq : F ((1-a)/2)=(1-a)*(1-3*a)^2/4 := by dsimp [F];ring
      rw [heq]
      positivity
    have hFx : 0 < F (1-2*a) := by
      have heq : F (1-2*a)=a*(1-2*a)*(1-3*a) := by dsimp [F];ring
      rw [heq]
      positivity
    have hgap : 0 < (1-2*a)-(1-a)/2 := by linarith
    have hid : F k*((1-2*a)-(1-a)/2) =
        ((1-2*a)-k)*F ((1-a)/2)+(k-(1-a)/2)*F (1-2*a)+
        (1-3*a)*((1-2*a)-(1-a)/2)*(k-(1-a)/2)*((1-2*a)-k) := by
      dsimp [F]
      ring
    have hFk : 0 < F k := by
      have hp := mul_pos (sub_pos.mpr hk) hFm
      have hq := mul_nonneg (sub_nonneg.mpr hm') hFx.le
      have hs := mul_nonneg (mul_nonneg (mul_nonneg hz.le hgap.le) (sub_nonneg.mpr hm')) (sub_nonneg.mpr hk.le)
      have ht : 0 < F k*((1-2*a)-(1-a)/2) := by rw [hid];linarith
      exact (mul_pos_iff_of_pos_right hgap).mp ht
    have hi : (2*a+s1 a k)*k-a*(1-a)=F k/(1-2*a) := by
      dsimp [s1,F]
      field_simp [hx.ne']
      ring
    have hi' : 0 < (2*a+s1 a k)*k-a*(1-a) := by rw [hi];exact div_pos hFk hx
    simp only [piBCB,piBC,piABC,if_neg hc,if_neg hm,if_pos hk]
    have hsimple : 2*r*a/2=r*a := by ring
    rw [hsimple]
    apply (le_div_iff₀ h1).mpr
    have hp := mul_pos hr hi'
    nlinarith

private lemma no_small (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) : ¬ (cond2a a k r ∧ cond2b a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hd : 0 < 2-5*a := by linarith
  have hkp : 0 < k := ha.trans hak
  rintro ⟨h2,hb2⟩
  by_cases hc : k < kCut a
  · have hcm : kCut a < (1-a)/2 := by
      unfold kCut
      rw [div_lt_iff₀ hd]
      nlinarith [mul_pos ha hz]
    have hm : k < (1-a)/2 := hc.trans hcm
    have hL : L0 a k r < LBC a k r := by
      simp only [cond2a,piIndepB,piBCB,piBC,if_pos hc] at h2
      have hi : 2*k*LBC a k r/2=k*LBC a k r := by ring
      rw [hi] at h2
      exact (mul_lt_mul_iff_right₀ hkp).mp h2
    have hY : LBC a k r = r*(a+s3 a k)/(1-2*a) := by
      have hV : r*a/k ≤ L0 a k r := by simp only [L0,if_pos hc];exact le_max_right _ _
      have hv : r*a/k < LBC a k r := hV.trans_lt hL
      simp only [LBC,if_pos hc] at hv ⊢
      exact max_eq_left (by cases lt_max_iff.mp hv with | inl h => exact h.le | inr h => exact False.elim (lt_irrefl _ h))
    let N := a*(1-a)*(1-3*a)+a*(1-5*a)*(k-a)+2*(1-3*a)*(k-a)^2
    have ht : (k-a)*(2-5*a) < (1-3*a)^2 := by
      have hh := (lt_div_iff₀ hd).mp hc
      nlinarith
    have hN : 0 < N := by
      have hbase := mul_pos (mul_pos ha h1) hz
      have hs := mul_nonneg (by linarith : 0 ≤ 2*(1-3*a)) (sq_nonneg (k-a))
      by_cases he : 0 ≤ 1-5*a
      · have hp := mul_nonneg (mul_nonneg ha.le he) (sub_nonneg.mpr hak.le)
        dsimp [N]
        linarith
      · have he' : 0 < a*(5*a-1) := mul_pos ha (by linarith)
        have ht' := mul_lt_mul_of_pos_left ht he'
        have hP : 0 < 20*a^2-15*a+3 := by nlinarith [sq_nonneg (40*a-15)]
        have hp := mul_pos (mul_pos ha hz) hP
        have hs' := mul_nonneg hs hd.le
        have hNd : 0 < N*(2-5*a) := by dsimp [N];nlinarith
        exact (mul_pos_iff_of_pos_right hd).mp hNd
    have hi : (2*a+s1 a k)-(1-2*a+k)*(a+s3 a k)/(1-2*a) = N/((1-a)*(1-2*a)) := by
      dsimp [s1,s3,N]
      field_simp [hx.ne',h1.ne']
      ring
    have hgap : (1-2*a+k)*(a+s3 a k)/(1-2*a) < 2*a+s1 a k := by
      have hh : 0 < (2*a+s1 a k)-(1-2*a+k)*(a+s3 a k)/(1-2*a) := by rw [hi];exact div_pos hN (mul_pos h1 hx)
      linarith
    have hAB : r*(2*a+s1 a k) ≤ piAB a k r := by
      simp only [piAB,LAB,if_pos hm]
      have hmax := mul_le_mul_of_nonneg_left (le_max_left (r*(2*a+s1 a k)/(1-a)) (r*a/k)) h1.le
      have hi : (1-a)*(r*(2*a+s1 a k)/(1-a))=r*(2*a+s1 a k) := by field_simp [h1.ne']
      rwa [hi] at hmax
    have hsum : piBCA a k r+piBCB a k r < r*(2*a+s1 a k) := by
      simp only [piBCA,piBCB,piBC,if_pos hc,hY]
      have hp := mul_lt_mul_of_pos_left hgap hr
      convert hp using 1 <;> first | rfl | ring
    exact (not_lt_of_ge hb2) (hsum.trans_le hAB)
  · have hbad : ¬ cond2a a k r := by
      simp only [cond2a,piIndepB,piBCB,piBC,if_neg hc,if_pos hk]
      split_ifs <;> linarith
    exact hbad h2

private lemma threshold_le (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (k ≤ kStar a → piAB a k r ≤ piIndepA a k r+piIndepB a k r) ∧
    (kStar a < k → piIndepA a k r+piIndepB a k r < piAB a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkp : 0 < k := ha.trans hak
  let A := r*(2*a+s1 a k)
  let B := (1-a)*(r*a/k)
  let C := r*(1-2*a+k)*(a+s2 a k)/(1-2*a)
  let D := r*a*(1-2*a+k)/k
  have hBD : B < D := by
    dsimp [B,D]
    apply (lt_div_iff₀ hkp).mpr
    have hc : (r*a/k)*k = r*a := div_mul_cancel₀ _ hkp.ne'
    have hp := mul_pos (mul_pos hr ha) (sub_pos.mpr hak)
    nlinarith
  have hid : A-D = r*(1-2*a-k)*((1-3*a)*k-a*(1-2*a))/((1-2*a)*k) := by
    dsimp [A,D,s1]
    field_simp [hx.ne',hkp.ne']
    ring
  have hsign : (k ≤ kStar a → A ≤ D) ∧ (kStar a < k → D < A) := by
    constructor
    · intro hh
      have hq : (1-3*a)*k-a*(1-2*a) ≤ 0 := by
        have hh' := (le_div_iff₀ hz).mp hh
        nlinarith
      have hh' : A-D ≤ 0 := by
        rw [hid]
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (mul_pos hr (sub_pos.mpr hk)).le hq) (mul_pos hx hkp).le
      linarith
    · intro hh
      have hq : 0 < (1-3*a)*k-a*(1-2*a) := by
        have hh' := (div_lt_iff₀ hz).mp hh
        nlinarith
      have hh' : 0 < A-D := by
        rw [hid]
        exact div_pos (mul_pos (mul_pos hr (sub_pos.mpr hk)) hq) (mul_pos hx hkp)
      linarith
  have hab : piAB a k r = if k < (1-a)/2 then max A B else A := by
    by_cases hm : k < (1-a)/2
    · simp only [piAB,LAB,if_pos hm]
      rw [mul_max_of_nonneg _ _ h1.le]
      dsimp [A,B]
      congr 1
      field_simp [h1.ne']
    · simp only [piAB,if_neg hm,if_pos hk,if_false]
      rfl
  by_cases hc : k < kCut a
  · have hi : piIndepA a k r+piIndepB a k r = max C D := by
      simp only [piIndepA,piIndepB,L0,if_pos hc]
      rw [← add_mul, mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1-2*a+k)]
      dsimp [C,D]
      congr 1 <;> ring
    have hCA : C < A := sigma_ineq a k r ha hb hak hc hr
    rw [hi,hab]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      split_ifs
      · exact (max_le hAD hBD.le).trans (le_max_right C D)
      · exact hAD.trans (le_max_right C D)
    · intro hh
      have hDA := hsign.2 hh
      have hiA : max C D < A := max_lt hCA hDA
      split_ifs
      · exact hiA.trans_le (le_max_left A B)
      · exact hiA
  · have hi : piIndepA a k r+piIndepB a k r = D := by
      simp only [piIndepA,piIndepB,if_neg hc,if_pos hk]
      dsimp [D]
      field_simp [hkp.ne']
    rw [hi,hab]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      split_ifs
      · exact max_le hAD hBD.le
      · exact hAD
    · intro hh
      have hDA := hsign.2 hh
      split_ifs
      · exact hDA.trans_le (le_max_left A B)
      · exact hDA


private lemma whole_structure (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hr : 0 < r) :
    (kStar a < k ∧ k < 1-2*a → {S | IsEquilibriumStructure a k r S} = {MarketStructure.mixed}) ∧
    (¬ (kStar a < k ∧ k < 1-2*a) → {S | IsEquilibriumStructure a k r S} = {MarketStructure.indep}) := by
  by_cases hk : k < 1-2*a
  · have hiff : cond1a a k r ↔ kStar a < k := by
      constructor
      · intro hh
        by_contra hn
        have hle := (threshold_le a k r ha hb hak hk hr).1 (le_of_not_gt hn)
        exact not_lt_of_ge hle hh
      · intro hh
        exact (threshold a k r ha hb hak hk hr).2 hh
    have h1b : cond1b a k r := Or.inr (remaining_C a k r ha hb hak hk hr)
    have hns := no_small a k r ha hb hak hk hr
    constructor
    · rintro ⟨hs,hk'⟩
      have h1a := hiff.mpr hs
      ext S
      cases S <;> simp [IsEquilibriumStructure,h1a,h1b,hns]
    · intro hn
      have hs : ¬ kStar a < k := by intro hh;exact hn ⟨hh,hk⟩
      have h1a : ¬ cond1a a k r := by intro hh;exact hs (hiff.mp hh)
      ext S
      cases S <;> simp [IsEquilibriumStructure,h1a,hns]
  · constructor
    · rintro ⟨hs,hk'⟩
      exact False.elim (hk hk')
    · intro hn
      exact high_capacity a k r ha hb (le_of_not_gt hk)

private lemma ab_quadratic (a k : ℝ) (ha : 0 < a) (hb : a < 1/3) (hk : k < 1-2*a) :
    (kAB₁ a ≤ k → 0 ≤ (1-a)*(1-2*a)*(k-a)-(1-3*a)*k^2) ∧
    (k < kAB₁ a → (1-a)*(1-2*a)*(k-a)-(1-3*a)*k^2 < 0) ∧
    (kAB₁ a < k → 0 < (1-a)*(1-2*a)*(k-a)-(1-3*a)*k^2) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  let D := (1-a)*(1-2*a)*(14*a^2-7*a+1)
  let M := (1-a)*(1-2*a)
  let F := fun t : ℝ => M*(t-a)-(1-3*a)*t^2
  have hD : 0 < D := by
    have hp : 0 < 14*a^2-7*a+1 := by nlinarith [sq_nonneg (28*a-7)]
    exact mul_pos (mul_pos h1 hx) hp
  have hs := Real.sq_sqrt hD.le
  have hsp := Real.sqrt_pos.mpr hD
  have hid (t : ℝ) : 4*(1-3*a)*F t=D-(2*(1-3*a)*t-M)^2 := by dsimp [D,M,F];ring
  have hFx : 0 < F (1-2*a) := by
    have he : F (1-2*a)=a*(1-2*a)*(1-3*a) := by dsimp [F,M];ring
    rw [he]
    positivity
  have htx : 2*(1-3*a)*(1-2*a)-M < Real.sqrt D := by
    have hid' := hid (1-2*a)
    have hp := mul_pos (by linarith : 0 < 4*(1-3*a)) hFx
    nlinarith
  have htk : 2*(1-3*a)*k-M < Real.sqrt D := by
    have hh := mul_lt_mul_of_pos_left hk (by linarith : 0 < 2*(1-3*a))
    linarith
  have hidk := hid k
  have hzp : 0 < 4*(1-3*a) := by linarith
  constructor
  · intro hh
    have hu : -Real.sqrt D ≤ 2*(1-3*a)*k-M := by
      have hh' := (div_le_iff₀ (by linarith : 0 < 2*(1-3*a))).mp hh
      change M-Real.sqrt D ≤ k*(2*(1-3*a)) at hh'
      nlinarith
    have hprod := mul_nonneg (by linarith : 0 ≤ Real.sqrt D+(2*(1-3*a)*k-M)) (by linarith : 0 ≤ Real.sqrt D-(2*(1-3*a)*k-M))
    have hmul : 0 ≤ 4*(1-3*a)*F k := by nlinarith
    exact (mul_nonneg_iff_of_pos_left hzp).mp hmul
  · constructor
    · intro hh
      have hu : 2*(1-3*a)*k-M < -Real.sqrt D := by
        have hh' := (lt_div_iff₀ (by linarith : 0 < 2*(1-3*a))).mp hh
        change k*(2*(1-3*a)) < M-Real.sqrt D at hh'
        nlinarith
      have hprod := mul_pos (by linarith : 0 < -(2*(1-3*a)*k-M)-Real.sqrt D) (by linarith : 0 < -(2*(1-3*a)*k-M)+Real.sqrt D)
      have hmul : 4*(1-3*a)*F k < 0 := by nlinarith
      rcases mul_neg_iff.mp hmul with h | h
      · exact h.2
      · linarith [h.1]
    · intro hh
      have hu : -Real.sqrt D < 2*(1-3*a)*k-M := by
        have hh' := (div_lt_iff₀ (by linarith : 0 < 2*(1-3*a))).mp hh
        change M-Real.sqrt D < k*(2*(1-3*a)) at hh'
        nlinarith
      have hprod := mul_pos (by linarith : 0 < Real.sqrt D+(2*(1-3*a)*k-M)) (by linarith : 0 < Real.sqrt D-(2*(1-3*a)*k-M))
      have hmul : 0 < 4*(1-3*a)*F k := by nlinarith
      exact (mul_pos_iff_of_pos_left hzp).mp hmul

private lemma ab_regions (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (OmegaAB₁ a k → LAB a k r=r*(2*a+s1 a k)/(1-a) ∧ piAB a k r=r*(2*a+s1 a k) ∧ piABC a k r=r*(2*a+s1 a k)*k/(1-a)) ∧
    (OmegaAB₂ a k → LAB a k r=r*a/k ∧ piAB a k r=r*a*(1-a)/k ∧ piABC a k r=r*a) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkp : 0 < k := ha.trans hak
  let F := (1-a)*(1-2*a)*(k-a)-(1-3*a)*k^2
  have hid : (2*a+s1 a k)*k-a*(1-a)=F/(1-2*a) := by
    dsimp [s1,F]
    field_simp [hx.ne']
    ring
  have hmF : (1-a)/2 ≤ k → 0 < F := by
    intro hm
    have hmid : kAB₁ a < (1-a)/2 := by
      unfold kAB₁
      apply (div_lt_iff₀ (by linarith : 0 < 2*(1-3*a))).mpr
      have hsq : 0 ≤ Real.sqrt ((1-a)*(1-2*a)*(14*a^2-7*a+1)) := Real.sqrt_nonneg _
      have hstrong : (1-a)*a < Real.sqrt ((1-a)*(1-2*a)*(14*a^2-7*a+1)) := by
        have hp : 0 < 14*a^2-7*a+1 := by nlinarith [sq_nonneg (28*a-7)]
        have hD : 0 ≤ (1-a)*(1-2*a)*(14*a^2-7*a+1) := (mul_pos (mul_pos h1 hx) hp).le
        have hs := Real.sq_sqrt hD
        have hid' : (1-a)*(1-2*a)*(14*a^2-7*a+1)-((1-a)*a)^2=(1-a)*(1-3*a)^3 := by ring
        have hpos := mul_pos h1 (pow_pos hz 3)
        nlinarith
      nlinarith
    exact (ab_quadratic a k ha hb hk).2.2 (hmid.trans_le hm)
  constructor
  · intro H
    have hF : 0 ≤ F := (ab_quadratic a k ha hb hk).1 H.2.2.1
    have hUV : r*a/k ≤ r*(2*a+s1 a k)/(1-a) := by
      apply (div_le_div_iff₀ hkp h1).mpr
      have hi' : 0 ≤ (2*a+s1 a k)*k-a*(1-a) := by rw [hid];exact div_nonneg hF hx.le
      have hp := mul_nonneg hr.le hi'
      nlinarith
    by_cases hm : k < (1-a)/2
    · simp only [LAB,piAB,piABC,if_pos hm,max_eq_left hUV]
      refine ⟨trivial,?_,?_⟩ <;> field_simp [h1.ne']
    · simp only [LAB,piAB,piABC,if_neg hm,if_pos hk]
      exact ⟨trivial,trivial,trivial⟩
  · intro H
    have hF : F < 0 := (ab_quadratic a k ha hb hk).2.1 H.2.2.2
    have hm : k < (1-a)/2 := by
      by_contra hn
      have hh := hmF (le_of_not_gt hn)
      linarith
    have hUV : r*(2*a+s1 a k)/(1-a) ≤ r*a/k := by
      apply (div_le_div_iff₀ h1 hkp).mpr
      have hi' : (2*a+s1 a k)*k-a*(1-a) < 0 := by rw [hid];exact div_neg_of_neg_of_pos hF hx
      have hp := mul_neg_of_pos_of_neg hr hi'
      nlinarith
    simp only [LAB,piAB,piABC,if_pos hm,max_eq_right hUV]
    refine ⟨trivial,?_,?_⟩ <;> field_simp [hkp.ne']

private lemma indep_bounds (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) : r*a ≤ piIndepB a k r ∧ piIndepB a k r ≤ piBCB a k r := by
  have hkp : 0 < k := ha.trans hak
  by_cases hc : k < kCut a
  · have H := (supports a k r ha hb hak hr).1
    have hV : r*a/k ≤ L0 a k r := by simp only [L0,if_pos hc];exact le_max_right _ _
    have hi : k*(r*a/k)=r*a := by field_simp [hkp.ne']
    have hp := mul_le_mul_of_nonneg_left hV hkp.le
    rw [hi] at hp
    simp only [piIndepB,piBCB,piBC,if_pos hc]
    have hbc : 2*k*LBC a k r/2=k*LBC a k r := by ring
    rw [hbc]
    exact ⟨hp,mul_le_mul_of_nonneg_left H hkp.le⟩
  · simp only [piIndepB,piBCB,piBC,if_neg hc,if_pos hk]
    split_ifs <;> constructor <;> linarith

private lemma C_strict (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) (hu : kAB₁ a < k) : piBCB a k r < piABC a k r := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hF := (ab_quadratic a k ha hb hk).2.2 hu
  have hi : (2*a+s1 a k)*k-a*(1-a)=((1-a)*(1-2*a)*(k-a)-(1-3*a)*k^2)/(1-2*a) := by
    unfold s1
    field_simp [hx.ne']
    ring
  have hnum : 0 < (2*a+s1 a k)*k-a*(1-a) := by rw [hi];exact div_pos hF hx
  have hV : r*a/k < r*(2*a+s1 a k)/(1-a) := by
    apply (div_lt_div_iff₀ hkp h1).mpr
    have hp := mul_pos hr hnum
    nlinarith
  have hY : r*(a+s3 a k)/(1-2*a) < r*(2*a+s1 a k)/(1-a) := by
    have hid : r*(2*a+s1 a k)/(1-a)-r*(a+s3 a k)/(1-2*a)=r*k*(1-3*a)/((1-a)*(1-2*a)) := by
      unfold s1 s3
      field_simp [hx.ne',h1.ne']
      ring
    have hp : 0 < r*(2*a+s1 a k)/(1-a)-r*(a+s3 a k)/(1-2*a) := by rw [hid];positivity
    linarith
  have H := (ab_regions a k r ha hb hak hk hr).1 ⟨ha,hb,hu.le,hk⟩
  rw [H.2.2]
  by_cases hc : k < kCut a
  · simp only [piBCB,piBC,LBC,if_pos hc]
    have hp := mul_lt_mul_of_pos_left (max_lt hY hV) hkp
    convert hp using 1 <;> first | rfl | ring
  · have hbc : piBCB a k r=r*a := by simp only [piBCB,piBC,if_neg hc];split_ifs <;> ring
    rw [hbc]
    apply (lt_div_iff₀ h1).mpr
    have hp := mul_pos hr hnum
    nlinarith

private lemma C_equal (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) (hu : k < kAB₁ a) :
    piIndepB a k r=piABC a k r ∧ piBCB a k r=piABC a k r := by
  have H := (ab_regions a k r ha hb hak hk hr).2 ⟨ha,hb,hak,hu⟩
  have hI := indep_bounds a k r ha hb hak hk hr
  have hC := remaining_C a k r ha hb hak hk hr
  have hBC : piBCB a k r=r*a := le_antisymm (by rwa [H.2.2] at hC) (hI.1.trans hI.2)
  have hIB : piIndepB a k r=r*a := le_antisymm (by simpa only [hBC] using hI.2) hI.1
  exact ⟨hIB.trans H.2.2.symm,hBC.trans H.2.2.symm⟩

private lemma sigma_small (a k : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k) (hc : k < kCut a) :
    (1-2*a+k)*(a+s3 a k)/(1-2*a) < 2*a+s1 a k := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hd : 0 < 2-5*a := by linarith
  let N := a*(1-a)*(1-3*a)+a*(1-5*a)*(k-a)+2*(1-3*a)*(k-a)^2
  have ht : (k-a)*(2-5*a) < (1-3*a)^2 := by
    have hh := (lt_div_iff₀ hd).mp hc
    nlinarith
  have hN : 0 < N := by
    have hbase := mul_pos (mul_pos ha h1) hz
    have hs := mul_nonneg (by linarith : 0 ≤ 2*(1-3*a)) (sq_nonneg (k-a))
    by_cases he : 0 ≤ 1-5*a
    · have hp := mul_nonneg (mul_nonneg ha.le he) (sub_nonneg.mpr hak.le)
      dsimp [N]
      linarith
    · have he' : 0 < a*(5*a-1) := mul_pos ha (by linarith)
      have ht' := mul_lt_mul_of_pos_left ht he'
      have hP : 0 < 20*a^2-15*a+3 := by nlinarith [sq_nonneg (40*a-15)]
      have hp := mul_pos (mul_pos ha hz) hP
      have hs' := mul_nonneg hs hd.le
      have hNd : 0 < N*(2-5*a) := by dsimp [N];nlinarith
      exact (mul_pos_iff_of_pos_right hd).mp hNd
  have hi : (2*a+s1 a k)-(1-2*a+k)*(a+s3 a k)/(1-2*a) = N/((1-a)*(1-2*a)) := by
    dsimp [s1,s3,N]
    field_simp [hx.ne',h1.ne']
    ring
  have hgap : (1-2*a+k)*(a+s3 a k)/(1-2*a) < 2*a+s1 a k := by
    have hh : 0 < (2*a+s1 a k)-(1-2*a+k)*(a+s3 a k)/(1-2*a) := by rw [hi];exact div_pos hN (mul_pos h1 hx)
    linarith
  exact hgap

private lemma threshold_small (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) (hm : k < (1-a)/2) :
    (k < kStar a → piAB a k r < piBCA a k r+piBCB a k r) ∧
    (kStar a < k → piBCA a k r+piBCB a k r < piAB a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hkp : 0 < k := ha.trans hak
  let A := r*(2*a+s1 a k)
  let B := (1-a)*(r*a/k)
  let C := r*(1-2*a+k)*(a+s3 a k)/(1-2*a)
  let D := r*a*(1-2*a+k)/k
  have hBD : B < D := by
    dsimp [B,D]
    apply (lt_div_iff₀ hkp).mpr
    have hc : (r*a/k)*k = r*a := div_mul_cancel₀ _ hkp.ne'
    have hp := mul_pos (mul_pos hr ha) (sub_pos.mpr hak)
    nlinarith
  have hid : A-D = r*(1-2*a-k)*((1-3*a)*k-a*(1-2*a))/((1-2*a)*k) := by
    dsimp [A,D,s1]
    field_simp [hx.ne',hkp.ne']
    ring
  have hsign : (k < kStar a → A < D) ∧ (kStar a < k → D < A) := by
    constructor
    · intro hh
      have hq : (1-3*a)*k-a*(1-2*a) < 0 := by
        have hh' := (lt_div_iff₀ hz).mp hh
        nlinarith
      have hh' : A-D < 0 := by
        rw [hid]
        exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hr (sub_pos.mpr hk)) hq) (mul_pos hx hkp)
      linarith
    · intro hh
      have hq : 0 < (1-3*a)*k-a*(1-2*a) := by
        have hh' := (div_lt_iff₀ hz).mp hh
        nlinarith
      have hh' : 0 < A-D := by
        rw [hid]
        exact div_pos (mul_pos (mul_pos hr (sub_pos.mpr hk)) hq) (mul_pos hx hkp)
      linarith
  have hab : piAB a k r = if k < (1-a)/2 then max A B else A := by
    by_cases hm : k < (1-a)/2
    · simp only [piAB,LAB,if_pos hm]
      rw [mul_max_of_nonneg _ _ h1.le]
      dsimp [A,B]
      congr 1
      field_simp [h1.ne']
    · simp only [piAB,if_neg hm,if_pos hk,if_false]
      rfl
  by_cases hc : k < kCut a
  · have hi : piBCA a k r+piBCB a k r = max C D := by
      simp only [piBCA,piBCB,piBC,LBC,if_pos hc]
      have hhalf : 2*k*max (r*(a+s3 a k)/(1-2*a)) (r*a/k)/2=k*max (r*(a+s3 a k)/(1-2*a)) (r*a/k) := by ring
      rw [hhalf]
      rw [← add_mul, mul_max_of_nonneg _ _ (by linarith : 0 ≤ 1-2*a+k)]
      dsimp [C,D]
      congr 1 <;> ring
    have hCA : C < A := by
      have H := mul_lt_mul_of_pos_left (sigma_small a k ha hb hak hc) hr
      simpa [C,A,mul_div_assoc,mul_assoc] using H
    rw [hi,hab]
    simp only [if_pos hm]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      exact (max_lt hAD hBD).trans_le (le_max_right C D)
    · intro hh
      have hDA := hsign.2 hh
      have hiA : max C D < A := max_lt hCA hDA
      exact hiA.trans_le (le_max_left A B)
  · have hi : piBCA a k r+piBCB a k r = D := by
      simp only [piBCA,piBCB,piBC,if_neg hc,if_pos hm]
      have hhalf : 2*r*a/2=r*a := by ring
      rw [hhalf]
      dsimp [D]
      field_simp [hkp.ne']
    rw [hi,hab]
    simp only [if_pos hm]
    constructor
    · intro hh
      have hAD := hsign.1 hh
      exact max_lt hAD hBD
    · intro hh
      have hDA := hsign.2 hh
      exact hDA.trans_le (le_max_left A B)


private lemma ab_vs_small (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (k < (1-a)/2 → (kStar a < k → piBCA a k r+piBCB a k r < piAB a k r) ∧
      (k < kStar a → piAB a k r < piBCA a k r+piBCB a k r)) ∧
    ((1-a)/2 < k → (piBCA a k r+piBCB a k r < piAB a k r ↔ k < (1-2*a)^2/(1-a))) := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  constructor
  · intro hm
    have H := threshold_small a k r ha hb hak hk hr hm
    exact ⟨H.2,H.1⟩
  · intro hm
    have hn : ¬ k < (1-a)/2 := by linarith
    have hc : ¬ k < kCut a := by
      have hcm : kCut a < (1-a)/2 := by
        unfold kCut
        rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
        nlinarith [mul_pos ha hz]
      linarith
    have hid : piAB a k r-(piBCA a k r+piBCB a k r)=
        r*(1-3*a)*((1-2*a)^2-(1-a)*k)/((1-a)*(1-2*a)) := by
      simp only [piAB,piBCA,piBCB,piBC,if_neg hc,if_neg hn,if_pos hk]
      unfold s1
      field_simp [hx.ne',h1.ne']
      ring
    rw [← sub_pos,hid]
    rw [div_pos_iff_of_pos_right (mul_pos h1 hx),mul_pos_iff_of_pos_left (mul_pos hr hz)]
    rw [sub_pos,lt_div_iff₀ h1]
    constructor <;> intro H <;> nlinarith only [H]

private lemma bc_positive (a k : ℝ) (ha : 0 < a) (hb : a < 1/3) (hm : k < (1-a)/2) :
    0 < (1-a)*(1-2*a)*k-2*(1-3*a)*k^2-a*(1-a)*(1-2*a) ↔ OmegaBC₁ a k := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  let M := (1-a)*(1-2*a)
  let D := M*(26*a^2-11*a+1)
  let E := fun t : ℝ => M*t-2*(1-3*a)*t^2-a*M
  have hid (t : ℝ) : 8*(1-3*a)*E t=D-(4*(1-3*a)*t-M)^2 := by dsimp [M,D,E];ring
  have h17 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  have hp17 := Real.sqrt_nonneg (17:ℝ)
  have h17p : (4:ℝ) < Real.sqrt 17 := by nlinarith
  constructor
  · intro H
    have H0 := H
    have H : 0 < E k := by dsimp [E,M];nlinarith only [H0]
    have ha4 : a < 1/4 := by
      by_contra hn
      have hge : 1/4 ≤ a := le_of_not_gt hn
      have he : E ((1-a)/2)=-a*(1-a)*(1-3*a)/2 := by dsimp [E,M];ring
      have hem : E ((1-a)/2) < 0 := by rw [he];have hh:=mul_pos (mul_pos ha h1) hz;linarith
      have hi : E ((1-a)/2)-E k=((1-a)/2-k)*(M-2*(1-3*a)*((1-a)/2+k)) := by dsimp [E];ring
      have hc : 0 ≤ M-2*(1-3*a)*((1-a)/2+k) := by
        have hprod := mul_nonneg h1.le (by linarith : 0 ≤ 4*a-1)
        have hh := mul_nonneg (by linarith : 0 ≤ 2*(1-3*a)) (sub_nonneg.mpr hm.le)
        dsimp [M]
        nlinarith
      have hnn := mul_nonneg (sub_nonneg.mpr hm.le) hc
      rw [← hi] at hnn
      linarith
    have hD : 0 < D := by
      have hp := mul_pos (by linarith : 0 < 8*(1-3*a)) H
      have hh := hid k
      nlinarith [sq_nonneg (4*(1-3*a)*k-M)]
    have hP : 0 < 26*a^2-11*a+1 := by
      by_contra hn
      have hh := mul_nonpos_of_nonneg_of_nonpos (mul_pos h1 hx).le (le_of_not_gt hn)
      change D ≤ 0 at hh
      linarith
    have hac : a < αBC₁ := by
      unfold αBC₁
      apply (lt_div_iff₀ (by norm_num : (0:ℝ)<52)).mpr
      have ht : 52*a-11 < Real.sqrt 17 := by linarith
      have hi : 17 < (52*a-11)^2 := by nlinarith
      nlinarith
    have hs := Real.sq_sqrt hD.le
    have hsp := Real.sqrt_nonneg D
    have hE := mul_pos (by linarith : 0 < 8*(1-3*a)) H
    have hi := hid k
    have hlo : -Real.sqrt D < 4*(1-3*a)*k-M := by nlinarith
    have hhi : 4*(1-3*a)*k-M < Real.sqrt D := by nlinarith
    refine ⟨ha,hac,?_,?_⟩
    · apply (div_lt_iff₀ (by linarith : 0 < 4*(1-3*a))).mpr
      change M-Real.sqrt D < k*(4*(1-3*a))
      nlinarith
    · apply (lt_div_iff₀ (by linarith : 0 < 4*(1-3*a))).mpr
      change k*(4*(1-3*a)) < M+Real.sqrt D
      nlinarith
  · rintro ⟨_,hac,hlo,hhi⟩
    have ht : a*52 < 11-Real.sqrt 17 := (lt_div_iff₀ (by norm_num : (0:ℝ)<52)).mp hac
    have hP : 0 < 26*a^2-11*a+1 := by
      have hp := mul_pos (by linarith : 0 < -(52*a-11)-Real.sqrt 17) (by linarith : 0 < -(52*a-11)+Real.sqrt 17)
      nlinarith
    have hD : 0 < D := mul_pos (mul_pos h1 hx) hP
    have hs := Real.sq_sqrt hD.le
    have hlo' := (div_lt_iff₀ (by linarith : 0 < 4*(1-3*a))).mp hlo
    have hhi' := (lt_div_iff₀ (by linarith : 0 < 4*(1-3*a))).mp hhi
    change M-Real.sqrt D < k*(4*(1-3*a)) at hlo'
    change k*(4*(1-3*a)) < M+Real.sqrt D at hhi'
    have hp := mul_pos (by linarith : 0 < Real.sqrt D+(4*(1-3*a)*k-M)) (by linarith : 0 < Real.sqrt D-(4*(1-3*a)*k-M))
    have hh := hid k
    have he : 0 < 8*(1-3*a)*E k := by nlinarith
    have hh := (mul_pos_iff_of_pos_left (by linarith : 0 < 8*(1-3*a))).mp he
    simpa only [E,M,mul_assoc] using hh

private lemma bc_active_cut (a k : ℝ) (ha : 0 < a) (hb : a < 1/3)
    (H : OmegaBC₁ a k) : k < kCut a := by
  have hx : 0 < 1-2*a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hd : 0 < 2-5*a := by linarith
  have h17 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 17)
  have hp17 := Real.sqrt_nonneg (17:ℝ)
  have h17p : (4:ℝ) < Real.sqrt 17 := by nlinarith
  have ha6 : a < 1/6 := by
    have hh := (lt_div_iff₀ (by norm_num : (0:ℝ)<52)).mp H.2.1
    linarith
  let M := (1-a)*(1-2*a)
  let D := M*(26*a^2-11*a+1)
  let E := fun t : ℝ => M*t-2*(1-3*a)*t^2-a*M
  have hP : 0 < 26*a^2-11*a+1 := by
    have ht := (lt_div_iff₀ (by norm_num : (0:ℝ)<52)).mp H.2.1
    have hp := mul_pos (by linarith : 0 < -(52*a-11)-Real.sqrt 17) (by linarith : 0 < -(52*a-11)+Real.sqrt 17)
    nlinarith
  have hD : 0 < D := mul_pos (mul_pos h1 hx) hP
  have hs := Real.sq_sqrt hD.le
  have hlo := (div_lt_iff₀ (by linarith : 0 < 4*(1-3*a))).mp H.2.2.1
  have hhi := (lt_div_iff₀ (by linarith : 0 < 4*(1-3*a))).mp H.2.2.2
  change M-Real.sqrt D < k*(4*(1-3*a)) at hlo
  change k*(4*(1-3*a)) < M+Real.sqrt D at hhi
  have hp := mul_pos (by linarith : 0 < Real.sqrt D+(4*(1-3*a)*k-M)) (by linarith : 0 < Real.sqrt D-(4*(1-3*a)*k-M))
  have hid : 8*(1-3*a)*E k=D-(4*(1-3*a)*k-M)^2 := by dsimp [M,D,E];ring
  have hEk : 0 < E k := by
    have hh : 0 < 8*(1-3*a)*E k := by nlinarith
    exact (mul_pos_iff_of_pos_left (by linarith : 0 < 8*(1-3*a))).mp hh
  have hEc : E (kCut a) = -a*(1-2*a)*(1-3*a)*(1-2*a-a^2)/(2-5*a)^2 := by
    dsimp [E,M,kCut]
    field_simp [hd.ne']
    ring_nf
    have hnn : 4-a*20+a^2*25 ≠ 0 := by nlinarith [sq_pos_of_pos hd]
    field_simp [hnn]
    ring
  have hEcn : E (kCut a) < 0 := by
    rw [hEc]
    have hh : 0 < 1-2*a-a^2 := by nlinarith
    exact div_neg_of_neg_of_pos (by have hp:=mul_pos (mul_pos (mul_pos ha hx) hz) hh; nlinarith) (pow_pos hd 2)
  have hder : M-4*(1-3*a)*kCut a < 0 := by
    have hid' : M-4*(1-3*a)*kCut a = -(1-2*a)*(19*a^2-13*a+2)/(2-5*a) := by
      dsimp [M,kCut]
      field_simp [hd.ne']
      ring_nf
      have hnn : 2-a*5 ≠ 0 := by linarith
      field_simp [hnn]
      ring
    rw [hid']
    have hpoly : 0 < 19*a^2-13*a+2 := by
      have hh := mul_pos (by linarith : 0 < 1-6*a) (by linarith : 0 < 2-7*a)
      nlinarith
    exact div_neg_of_neg_of_pos (by have hp:=mul_pos hx hpoly;nlinarith) hd
  by_contra hn
  have hge := le_of_not_gt hn
  have hi : E k=E (kCut a)+(k-kCut a)*(M-4*(1-3*a)*kCut a)-2*(1-3*a)*(k-kCut a)^2 := by dsimp [E];ring
  have hn1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hge) hder.le
  have hn2 := mul_nonneg (by linarith : 0 ≤ 2*(1-3*a)) (sq_nonneg (k-kCut a))
  linarith

private lemma bc_formula_gap (a k r : ℝ) (hx : 1-2*a ≠ 0) (h1 : 1-a ≠ 0) (hk : k ≠ 0) :
    r*(a+s3 a k)/(1-2*a)-r*a/k =
      r*((1-a)*(1-2*a)*k-2*(1-3*a)*k^2-a*(1-a)*(1-2*a))/((1-a)*(1-2*a)*k) := by
  unfold s3
  field_simp [hx,h1,hk]
  ring_nf
  have hn : 1-a*2 ≠ 0 := by intro hh;apply hx;linarith
  field_simp [hn]
  ring

private lemma bc_regions (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (OmegaBC₁ a k → LBC a k r=r*(a+s3 a k)/(1-2*a) ∧ piBCA a k r=r*(a+s3 a k) ∧ piBC a k r=2*r*(a+s3 a k)*k/(1-2*a)) ∧
    (OmegaBC₂ a k → LBC a k r=r*a/k ∧ piBCA a k r=r*a*(1-2*a)/k ∧ piBC a k r=2*r*a) ∧
    (OmegaBC₃ a k → LBC a k r=2*r*a/(1-a) ∧ piBCA a k r=2*r*a*(1-2*a)/(1-a) ∧ piBC a k r=2*r*a) := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hcm : kCut a < (1-a)/2 := by
    unfold kCut
    rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
    nlinarith [mul_pos ha hz]
  constructor
  · intro H
    have hc := bc_active_cut a k ha hb H
    have hm := hc.trans hcm
    have hE := (bc_positive a k ha hb hm).mpr H
    have hY : r*a/k < r*(a+s3 a k)/(1-2*a) := by
      have hh : 0 < r*(a+s3 a k)/(1-2*a)-r*a/k := by
        rw [bc_formula_gap a k r hx.ne' h1.ne' hkp.ne']
        exact div_pos (mul_pos hr hE) (mul_pos (mul_pos h1 hx) hkp)
      linarith
    simp only [LBC,piBCA,piBC,if_pos hc,max_eq_left hY.le]
    refine ⟨trivial,?_,?_⟩ <;> field_simp [hx.ne'] <;> ring
  · constructor
    · intro H
      have hm := H.2.2.2.2
      have hE : (1-a)*(1-2*a)*k-2*(1-3*a)*k^2-a*(1-a)*(1-2*a) ≤ 0 := by
        by_contra hn
        exact H.1 ((bc_positive a k ha hb hm).mp (lt_of_not_ge hn))
      have hY : r*(a+s3 a k)/(1-2*a) ≤ r*a/k := by
        have hh : r*(a+s3 a k)/(1-2*a)-r*a/k ≤ 0 := by
          rw [bc_formula_gap a k r hx.ne' h1.ne' hkp.ne']
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr.le hE) (mul_pos (mul_pos h1 hx) hkp).le
        linarith
      by_cases hc : k < kCut a
      · simp only [LBC,piBCA,piBC,if_pos hc,max_eq_right hY]
        refine ⟨trivial,?_,?_⟩ <;> field_simp [hkp.ne'] <;> ring
      · simp only [LBC,piBCA,piBC,if_neg hc,if_pos hm]
        exact ⟨trivial,trivial,trivial⟩
    · intro H
      have hn : ¬ k < (1-a)/2 := not_lt.mpr H.2.2.1
      have hc : ¬ k < kCut a := by linarith [H.2.2.1]
      simp [LBC,piBCA,piBC,if_neg hc,if_neg hn]

private lemma bc_comparisons (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (OmegaBC₁ a k → piIndepB a k r < piBCB a k r) ∧
    (OmegaBC₂ a k → piIndepB a k r=piBCB a k r) ∧
    ((1-a)/2 < k → piIndepB a k r=piBCB a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  constructor
  · intro H
    have hc := bc_active_cut a k ha hb H
    have hcm : kCut a < (1-a)/2 := by
      unfold kCut
      rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
      nlinarith [mul_pos ha hz]
    have hE := (bc_positive a k ha hb (hc.trans hcm)).mpr H
    have hV : r*a/k < r*(a+s3 a k)/(1-2*a) := by
      have hh : 0 < r*(a+s3 a k)/(1-2*a)-r*a/k := by
        rw [bc_formula_gap a k r hx.ne' h1.ne' hkp.ne']
        exact div_pos (mul_pos hr hE) (mul_pos (mul_pos h1 hx) hkp)
      linarith
    have hX : r*(a+s2 a k)/(1-2*a) < r*(a+s3 a k)/(1-2*a) := by
      apply (div_lt_div_iff_of_pos_right hx).mpr
      exact mul_lt_mul_of_pos_left (by linarith [s_difference a k ha hb hak hc]) hr
    have hF := (bc_regions a k r ha hb hak hk hr).1 H
    simp only [piIndepB,piBCB,piBC,L0,if_pos hc,hF.1]
    have hp := mul_lt_mul_of_pos_left (max_lt hX hV) hkp
    convert hp using 1 <;> first | rfl | ring
  · constructor
    · intro H
      have hF := (bc_regions a k r ha hb hak hk hr).2.1 H
      have hbc : piBCB a k r=r*a := by unfold piBCB;rw [hF.2.2];ring
      have hI := indep_bounds a k r ha hb hak hk hr
      rw [hbc]
      exact le_antisymm (by simpa only [hbc] using hI.2) hI.1
    · intro hm
      have hcm : kCut a < (1-a)/2 := by
        unfold kCut
        rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
        nlinarith [mul_pos ha hz]
      have hc : ¬ k < kCut a := by linarith
      have hn : ¬ k < (1-a)/2 := by linarith
      simp only [piIndepB,piBCB,piBC,if_neg hc,if_neg hn,if_pos hk]
      ring

private lemma bc_sums (a k r : ℝ) (ha : 0 < a) (hb : a < 1/3) (hak : a < k)
    (hk : k < 1-2*a) (hr : 0 < r) :
    (OmegaBC₁ a k → piIndepA a k r+piIndepB a k r < piBCA a k r+piBCB a k r) ∧
    (OmegaBC₂ a k → piIndepA a k r+piIndepB a k r = piBCA a k r+piBCB a k r) ∧
    ((1-a)/2 < k → piIndepA a k r+piIndepB a k r < piBCA a k r+piBCB a k r) := by
  have hx : 0 < 1-2*a := by linarith
  have h1 : 0 < 1-a := by linarith
  have hz : 0 < 1-3*a := by linarith
  have hkp : 0 < k := ha.trans hak
  have hcm : kCut a < (1-a)/2 := by
    unfold kCut
    rw [div_lt_iff₀ (by linarith : 0 < 2-5*a)]
    nlinarith [mul_pos ha hz]
  have hsum (hm : k < (1-a)/2) :
      piIndepA a k r+piIndepB a k r = ((1-2*a+k)/k)*piIndepB a k r ∧
      piBCA a k r+piBCB a k r = ((1-2*a+k)/k)*piBCB a k r := by
    by_cases hc : k < kCut a
    · simp only [piIndepA,piIndepB,piBCA,piBCB,piBC,if_pos hc]
      constructor <;> field_simp [hkp.ne'] <;> ring
    · simp only [piIndepA,piIndepB,piBCA,piBCB,piBC,if_neg hc,if_pos hk,if_pos hm]
      constructor <;> field_simp [hkp.ne'] <;> ring
  constructor
  · intro H
    have hm := (bc_active_cut a k ha hb H).trans hcm
    rw [(hsum hm).1,(hsum hm).2]
    exact mul_lt_mul_of_pos_left ((bc_comparisons a k r ha hb hak hk hr).1 H) (div_pos (by linarith) hkp)
  · constructor
    · intro H
      rw [(hsum H.2.2.2.2).1,(hsum H.2.2.2.2).2,(bc_comparisons a k r ha hb hak hk hr).2.1 H]
    · intro hm
      have hc : ¬ k < kCut a := by linarith
      have hn : ¬ k < (1-a)/2 := by linarith
      have hid : (piBCA a k r+piBCB a k r)-(piIndepA a k r+piIndepB a k r)=
          r*a*(1-2*a)*(2*k-(1-a))/((1-a)*k) := by
        simp only [piBCA,piBCB,piBC,piIndepA,piIndepB,if_neg hc,if_neg hn,if_pos hk]
        field_simp [h1.ne',hkp.ne']
        ring
      have hp : 0 < (piBCA a k r+piBCB a k r)-(piIndepA a k r+piIndepB a k r) := by
        rw [hid]
        exact div_pos (mul_pos (mul_pos (mul_pos hr ha) hx) (by linarith)) (mul_pos h1 hkp)
      linarith

theorem solution (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (OmegaBC₁ α k →
      LBC α k r = r * (α + s3 α k) / (1 - 2 * α) ∧
      piBCA α k r = r * (α + s3 α k) ∧
      piBC α k r = 2 * r * (α + s3 α k) * k / (1 - 2 * α)) ∧
    (OmegaBC₂ α k →
      LBC α k r = r * α / k ∧
      piBCA α k r = r * α * (1 - 2 * α) / k ∧
      piBC α k r = 2 * r * α) ∧
    (OmegaBC₃ α k →
      LBC α k r = 2 * r * α / (1 - α) ∧
      piBCA α k r = 2 * r * α * (1 - 2 * α) / (1 - α) ∧
      piBC α k r = 2 * r * α) := by
  exact bc_regions α k r hα0 hα3 hαk hk hr

#print axioms solution

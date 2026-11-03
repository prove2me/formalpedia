-- Prove2me | solution 1 for FracRiccati.Radius.kershaw_A_41
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:29:26.405417+00:00
-- url     : https://prove2.me/submissions/b0cf5f18-11d8-4bb3-bb46-d9ef5def541e

import Mathlib

namespace Aux_FRR_K41
open Filter Topology

/-- The auxiliary function `g(y) = log((y+1)/(y+s)) - (1-s) log((y+c+1)/(y+c))`. -/
noncomputable def g (s c : ℝ) (y : ℝ) : ℝ :=
  Real.log (y + 1) - Real.log (y + s) - (1 - s) * (Real.log (y + c + 1) - Real.log (y + c))

lemma g_hasDeriv (s c y : ℝ) (hs : 0 < s) (hc : 0 ≤ c) (hy : 0 < y) :
    HasDerivAt (g s c) ((1 - s) * (1 / ((y + c) * (y + c + 1)) - 1 / ((y + 1) * (y + s)))) y := by
  have hlog : ∀ a : ℝ, 0 < y + a → HasDerivAt (fun z => Real.log (z + a)) (1 / (y + a)) y := by
    intro a ha
    have := ((hasDerivAt_id y).add_const a).log (ne_of_gt ha)
    simpa using this
  have h := (((hlog 1 (by linarith)).sub (hlog s (by linarith))).sub
    (((hlog (c + 1) (by linarith)).sub (hlog c (by linarith))).const_mul (1 - s)))
  have e : (1 / (y + 1) - 1 / (y + s) - (1 - s) * (1 / (y + (c + 1)) - 1 / (y + c))) =
      (1 - s) * (1 / ((y + c) * (y + c + 1)) - 1 / ((y + 1) * (y + s))) := by
    have : 0 < y + c := by linarith
    field_simp
    ring
  rw [e] at h
  have hfun : g s c = (fun z => Real.log (z + 1) - Real.log (z + s) -
      (1 - s) * (Real.log (z + (c + 1)) - Real.log (z + c))) := by
    funext z; simp only [g]; ring_nf
  rw [hfun]; exact h

lemma g_cont (s c : ℝ) (hs : 0 < s) (hc : 0 ≤ c) : ContinuousOn (g s c) (Set.Ioi 0) :=
  fun y hy => (g_hasDeriv s c y hs hc hy).continuousAt.continuousWithinAt

lemma tend_log_ratio (a b : ℝ) :
    Tendsto (fun y : ℝ => Real.log (y + a) - Real.log (y + b)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => 1 + (a - b) / (y + b)) atTop (𝓝 1) := by
    have : Tendsto (fun y : ℝ => (a - b) / (y + b)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ b tendsto_id)
    simpa using this.const_add 1
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h1
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (max (-a) (-b))] with y hy
  have ha : 0 < y + a := by have := le_max_left (-a) (-b); linarith
  have hb : 0 < y + b := by have := le_max_right (-a) (-b); linarith
  simp only [Function.comp]
  rw [← Real.log_div ha.ne' hb.ne']
  congr 1
  field_simp
  ring

lemma g_tend (s c : ℝ) : Tendsto (g s c) atTop (𝓝 0) := by
  have := (tend_log_ratio 1 s).sub (((tend_log_ratio (c + 1) c)).const_mul (1 - s))
  simp only [mul_zero, sub_zero] at this
  refine this.congr' (Eventually.of_forall fun y => ?_)
  simp only [g]; ring_nf

/-- lower case: `g < 0` when `(y+c)(y+c+1) < (y+1)(y+s)`. -/
lemma g_neg (s c : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 ≤ c)
    (hq : ∀ y > 0, (y + c) * (y + c + 1) < (y + 1) * (y + s)) (y : ℝ) (hy : 0 < y) :
    g s c y < 0 := by
  have hmono : StrictMonoOn (g s c) (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (g_cont s c hs0 hc)
    intro z hz
    rw [interior_Ioi] at hz
    rw [(g_hasDeriv s c z hs0 hc hz).deriv]
    have hz' : (0 : ℝ) < z := hz
    have h1 : 0 < (z + c) * (z + c + 1) := by positivity
    have h2 := hq z hz'
    apply mul_pos (by linarith)
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt h1 h2
  have h1 : g s c y < g s c (y + 1) := hmono hy (by simp; linarith) (by linarith)
  have h2 : g s c (y + 1) ≤ 0 := by
    apply ge_of_tendsto (g_tend s c)
    filter_upwards [eventually_gt_atTop (y + 1)] with z hz
    exact (hmono (by simp; linarith) (by simp; linarith) hz).le
  linarith

/-- upper case: `g > 0` when `(y+1)(y+s) < (y+c)(y+c+1)`. -/
lemma g_pos (s c : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hc : 0 ≤ c)
    (hq : ∀ y > 0, (y + 1) * (y + s) < (y + c) * (y + c + 1)) (y : ℝ) (hy : 0 < y) :
    0 < g s c y := by
  have hanti : StrictAntiOn (g s c) (Set.Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) (g_cont s c hs0 hc)
    intro z hz
    rw [interior_Ioi] at hz
    rw [(g_hasDeriv s c z hs0 hc hz).deriv]
    have hz' : (0 : ℝ) < z := hz
    have h1 : 0 < (z + 1) * (z + s) := by positivity
    have h2 := hq z hz'
    apply mul_neg_of_pos_of_neg (by linarith)
    rw [sub_neg]
    exact one_div_lt_one_div_of_lt h1 h2
  have h1 : g s c (y + 1) < g s c y := hanti hy (by simp; linarith) (by linarith)
  have h2 : 0 ≤ g s c (y + 1) := by
    apply le_of_tendsto (g_tend s c)
    filter_upwards [eventually_gt_atTop (y + 1)] with z hz
    exact (hanti (by simp; linarith) (by simp; linarith) hz).le
  linarith

/-- Wendel-type upper bound from log-convexity: `Γ(x+s) ≤ x^s Γ(x)` for `s ∈ (0,1)`. -/
lemma gamma_upper (x s : ℝ) (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.Gamma (x + s) ≤ x ^ s * Real.Gamma x := by
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have key := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1)
    (a := 1 - s) (b := s) hx (by linarith) (by linarith) hs0 (by ring)
  have e1 : (1 - s) * x + s * (x + 1) = x + s := by ring
  rw [e1, Real.Gamma_add_one hx.ne', Real.mul_rpow hx.le hG.le] at key
  calc Real.Gamma (x + s) ≤ Real.Gamma x ^ (1 - s) * (x ^ s * Real.Gamma x ^ s) := key
    _ = x ^ s * (Real.Gamma x ^ (1 - s) * Real.Gamma x ^ s) := by ring
    _ = x ^ s * Real.Gamma x := by
      rw [← Real.rpow_add hG, show 1 - s + s = 1 by ring, Real.rpow_one]

/-- Wendel-type lower bound: `x Γ(x) ≤ Γ(x+s) (x+s)^{1-s}` for `s ∈ (0,1)`. -/
lemma gamma_lower (z s : ℝ) (hz : 0 < z) (hs0 : 0 < s) (hs1 : s < 1) :
    z * Real.Gamma z ≤ Real.Gamma (z + s) * (z + s) ^ (1 - s) := by
  have hzs : 0 < z + s := by linarith
  have hG : 0 < Real.Gamma (z + s) := Real.Gamma_pos_of_pos hzs
  rw [← Real.Gamma_add_one hz.ne']
  have key := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := z + s) (t := z + s + 1)
    (a := s) (b := 1 - s) hzs (by linarith) hs0 (by linarith) (by ring)
  have e1 : s * (z + s) + (1 - s) * (z + s + 1) = z + 1 := by ring
  rw [e1, Real.Gamma_add_one hzs.ne', Real.mul_rpow hzs.le hG.le] at key
  calc Real.Gamma (z + 1) ≤ Real.Gamma (z + s) ^ s * ((z + s) ^ (1 - s) * Real.Gamma (z + s) ^ (1 - s)) := key
    _ = (Real.Gamma (z + s) ^ s * Real.Gamma (z + s) ^ (1 - s)) * (z + s) ^ (1 - s) := by ring
    _ = Real.Gamma (z + s) * (z + s) ^ (1 - s) := by
      rw [← Real.rpow_add hG, show s + (1 - s) = 1 by ring, Real.rpow_one]

/-- `F(y) = (y+c)^{1-s} Γ(y+s)/Γ(y+1)`. -/
noncomputable def F (s c y : ℝ) : ℝ := (y + c) ^ (1 - s) * Real.Gamma (y + s) / Real.Gamma (y + 1)

lemma F_pos (s c y : ℝ) (hs : 0 < s) (hc : 0 ≤ c) (hy : 0 < y) : 0 < F s c y := by
  unfold F
  have := Real.Gamma_pos_of_pos (show 0 < y + s by linarith)
  have := Real.Gamma_pos_of_pos (show 0 < y + 1 by linarith)
  have : 0 < y + c := by linarith
  positivity

lemma F_step (s c y : ℝ) (hs : 0 < s) (hc : 0 ≤ c) (hy : 0 < y) :
    F s c (y + 1) = F s c y * (((y + c + 1) / (y + c)) ^ (1 - s) * ((y + s) / (y + 1))) := by
  unfold F
  have hys : 0 < y + s := by linarith
  have hyc : 0 < y + c := by linarith
  have hG1 := Real.Gamma_pos_of_pos hys
  have hG2 := Real.Gamma_pos_of_pos (show 0 < y + 1 by linarith)
  rw [show y + 1 + s = (y + s) + 1 by ring, Real.Gamma_add_one hys.ne',
    Real.Gamma_add_one (show y + 1 ≠ 0 by linarith), show y + 1 + c = y + c + 1 by ring,
    Real.div_rpow (by linarith) hyc.le]
  have : 0 < (y + c) ^ (1 - s) := by positivity
  field_simp

lemma R_gt (s c y : ℝ) (hs : 0 < s) (hc : 0 ≤ c) (hy : 0 < y) (hg : g s c y < 0) :
    1 < ((y + c + 1) / (y + c)) ^ (1 - s) * ((y + s) / (y + 1)) := by
  have hys : 0 < y + s := by linarith
  have hyc : 0 < y + c := by linarith
  have h : (y + 1) / (y + s) < ((y + c + 1) / (y + c)) ^ (1 - s) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_div (by linarith) hys.ne', Real.log_div (by linarith) hyc.ne']
    unfold g at hg; linarith
  rw [div_lt_iff₀ hys] at h
  rw [mul_div_assoc', lt_div_iff₀ (by linarith)]
  linarith

lemma R_lt (s c y : ℝ) (hs : 0 < s) (hc : 0 ≤ c) (hy : 0 < y) (hg : 0 < g s c y) :
    ((y + c + 1) / (y + c)) ^ (1 - s) * ((y + s) / (y + 1)) < 1 := by
  have hys : 0 < y + s := by linarith
  have hyc : 0 < y + c := by linarith
  have h : ((y + c + 1) / (y + c)) ^ (1 - s) < (y + 1) / (y + s) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_div (by linarith) hys.ne', Real.log_div (by linarith) hyc.ne']
    unfold g at hg; linarith
  rw [lt_div_iff₀ hys] at h
  rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
  linarith

lemma tend_ratio_rpow (a b e : ℝ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + a) / ((n : ℝ) + b)) ^ e) atTop (𝓝 1) := by
  have h1 : Tendsto (fun y : ℝ => 1 + (a - b) / (y + b)) atTop (𝓝 1) := by
    have : Tendsto (fun y : ℝ => (a - b) / (y + b)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ b tendsto_id)
    simpa using this.const_add 1
  have h2 := ((Real.continuousAt_rpow_const 1 e (Or.inl one_ne_zero)).tendsto).comp
    (h1.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  rw [Real.one_rpow] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (⌈max (-a) (-b)⌉₊)] with n hn
  have hn' : max (-a) (-b) < (n : ℝ) := by
    have := Nat.le_ceil (max (-a) (-b))
    have : (⌈max (-a) (-b)⌉₊ : ℝ) < n := by exact_mod_cast hn
    linarith
  have hb : 0 < (n : ℝ) + b := by have := le_max_right (-a) (-b); linarith
  simp only [Function.comp]
  congr 1
  field_simp
  ring

end Aux_FRR_K41

open Aux_FRR_K41 in
theorem solution (x s : ℝ) (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    (x + s / 2) ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
    Real.Gamma (x + 1) / Real.Gamma (x + s) < (x - 1 / 2 + Real.sqrt (s + 1 / 4)) ^ (1 - s) := by
  have hGs : 0 < Real.Gamma (x + s) := Real.Gamma_pos_of_pos (by linarith)
  have hG1 : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  constructor
  · -- lower bound, `c = s/2`
    set c := s / 2 with hcdef
    have hc : 0 ≤ c := by positivity
    have hq : ∀ y > 0, (y + c) * (y + c + 1) < (y + 1) * (y + s) := by
      intro y hy; rw [hcdef]; nlinarith
    have hinc : ∀ y > 0, F s c y < F s c (y + 1) := by
      intro y hy
      rw [F_step s c y hs0 hc hy]
      have := R_gt s c y hs0 hc hy (g_neg s c hs0 hs1 hc hq y hy)
      have := F_pos s c y hs0 hc hy
      nlinarith
    have hbound : ∀ y > 0, F s c y ≤ ((y + c) / y) ^ (1 - s) := by
      intro y hy
      unfold F
      have hW := gamma_upper y s hy hs0 hs1
      have hGy := Real.Gamma_pos_of_pos hy
      rw [Real.Gamma_add_one hy.ne', Real.div_rpow (by linarith) hy.le,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have e0 : y ^ s * y ^ (1 - s) = y := by
        rw [← Real.rpow_add hy, show s + (1 - s) = 1 by ring, Real.rpow_one]
      have e : y ^ s * Real.Gamma y * y ^ (1 - s) = y * Real.Gamma y := by
        rw [show y ^ s * Real.Gamma y * y ^ (1 - s) = (y ^ s * y ^ (1 - s)) * Real.Gamma y by ring, e0]
      have : 0 ≤ (y + c) ^ (1 - s) := by positivity
      calc (y + c) ^ (1 - s) * Real.Gamma (y + s) * y ^ (1 - s)
          ≤ (y + c) ^ (1 - s) * (y ^ s * Real.Gamma y) * y ^ (1 - s) := by gcongr
        _ = (y + c) ^ (1 - s) * (y * Real.Gamma y) := by rw [← e]; ring
    have hchain : ∀ n : ℕ, F s c (x + 1) ≤ F s c (x + 1 + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        refine ih.trans (le_of_lt ?_)
        have := hinc (x + 1 + n) (by positivity)
        rwa [show x + 1 + (n : ℝ) + 1 = x + 1 + ((n + 1 : ℕ) : ℝ) by push_cast; ring] at this
    have hle1 : F s c (x + 1) ≤ 1 := by
      have ht := tend_ratio_rpow (x + 1 + c) (x + 1) (1 - s)
      apply ge_of_tendsto ht
      filter_upwards with n
      refine (hchain n).trans ?_
      have := hbound (x + 1 + n) (by positivity)
      rw [show ((n : ℝ) + (x + 1 + c)) / ((n : ℝ) + (x + 1)) = (x + 1 + n + c) / (x + 1 + n) by ring]
      exact this
    have hlt : F s c x < 1 := (hinc x hx).trans_le hle1
    unfold F at hlt
    rw [div_lt_one hG1] at hlt
    rw [lt_div_iff₀ hGs]
    linarith
  · -- upper bound, `c = √(s+1/4) - 1/2`
    set c := Real.sqrt (s + 1 / 4) - 1 / 2 with hcdef
    have hsq : Real.sqrt (s + 1 / 4) ^ 2 = s + 1 / 4 := Real.sq_sqrt (by linarith)
    have hsqgt : (s + 1) / 2 < Real.sqrt (s + 1 / 4) := by
      rw [Real.lt_sqrt (by linarith)]; nlinarith
    have hc : 0 ≤ c := by rw [hcdef]; linarith
    have hcc : c * (c + 1) = s := by rw [hcdef]; nlinarith
    have hq : ∀ y > 0, (y + 1) * (y + s) < (y + c) * (y + c + 1) := by
      intro y hy
      have : s < 2 * c := by rw [hcdef]; linarith
      nlinarith
    have hdec : ∀ y > 0, F s c (y + 1) < F s c y := by
      intro y hy
      rw [F_step s c y hs0 hc hy]
      have := R_lt s c y hs0 hc hy (g_pos s c hs0 hs1 hc hq y hy)
      have := F_pos s c y hs0 hc hy
      nlinarith
    have hbound : ∀ y > 0, ((y + c) / (y + s)) ^ (1 - s) ≤ F s c y := by
      intro y hy
      unfold F
      have hW := gamma_lower y s hy hs0 hs1
      have hGy := Real.Gamma_pos_of_pos hy
      have hys : 0 < y + s := by linarith
      rw [Real.Gamma_add_one hy.ne', Real.div_rpow (by linarith) hys.le,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ (y + c) ^ (1 - s) := by positivity
      calc (y + c) ^ (1 - s) * (y * Real.Gamma y)
          ≤ (y + c) ^ (1 - s) * (Real.Gamma (y + s) * (y + s) ^ (1 - s)) := by gcongr
        _ = (y + c) ^ (1 - s) * Real.Gamma (y + s) * (y + s) ^ (1 - s) := by ring
    have hchain : ∀ n : ℕ, F s c (x + 1 + n) ≤ F s c (x + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        refine (le_of_lt ?_).trans ih
        have := hdec (x + 1 + n) (by positivity)
        rwa [show x + 1 + (n : ℝ) + 1 = x + 1 + ((n + 1 : ℕ) : ℝ) by push_cast; ring] at this
    have hge1 : 1 ≤ F s c (x + 1) := by
      have ht := tend_ratio_rpow (x + 1 + c) (x + 1 + s) (1 - s)
      apply le_of_tendsto ht
      filter_upwards with n
      refine le_trans ?_ (hchain n)
      have := hbound (x + 1 + n) (by positivity)
      rw [show ((n : ℝ) + (x + 1 + c)) / ((n : ℝ) + (x + 1 + s)) = (x + 1 + n + c) / (x + 1 + n + s) by ring]
      exact this
    have hgt : 1 < F s c x := hge1.trans_lt (hdec x hx)
    unfold F at hgt
    rw [one_lt_div hG1] at hgt
    rw [div_lt_iff₀ hGs, show x - 1 / 2 + Real.sqrt (s + 1 / 4) = x + c by rw [hcdef]; ring]
    linarith

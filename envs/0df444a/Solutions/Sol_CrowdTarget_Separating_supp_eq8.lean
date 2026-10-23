-- Prove2me | solution 1 for CrowdTarget.Separating.supp_eq8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:11:57.64567+00:00
-- url     : https://prove2.me/submissions/d978ecd3-3c39-4827-9049-010db96afb0e

import Mathlib
import Definitions.Def_CrowdTarget_Separating_Setting

open CrowdTarget.Separating MeasureTheory

namespace CTSol

noncomputable def F (n S C q : ℝ) : ℝ := (q*n - C)*(q*n + C - 2*S)/(2*n*q)

noncomputable def Pi (n S C q : ℝ) : ℝ := if 0 < q ∧ C ≤ q*n then F n S C q else 0

lemma cp_eq (P : Params) (hn : 0 < P.Nbar) (k S C p : ℝ) (hC : 0 < C) :
    campaignProfit P k S C p = Pi P.Nbar S C (k*p) := by
  unfold campaignProfit Pi
  split_ifs with h
  · obtain ⟨hq, hle⟩ := h
    have hset : Set.Icc 0 P.Nbar ∩ {N : ℝ | C ≤ k * p * N} = Set.Icc (C/(k*p)) P.Nbar := by
      ext N
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq]
      rw [div_le_iff₀ hq]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by linarith, h1⟩
      · rintro ⟨h2, h1⟩
        refine ⟨⟨?_, h1⟩, by linarith⟩
        by_contra hneg; push_neg at hneg; nlinarith
    have hab : C/(k*p) ≤ P.Nbar := by rw [div_le_iff₀ hq]; linarith
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have hk : k ≠ 0 := left_ne_zero_of_mul hq.ne'
    have hp : p ≠ 0 := right_ne_zero_of_mul hq.ne'
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    unfold F; simp only [smul_eq_mul]; field_simp; ring
  · have hset : Set.Icc 0 P.Nbar ∩ {N : ℝ | C ≤ k * p * N} = ∅ := by
      ext N
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨h0, h1⟩, h2⟩
      apply h
      by_cases hq : 0 < k*p
      · exact ⟨hq, by nlinarith⟩
      · push_neg at hq; nlinarith
    rw [hset]; simp

lemma F_nonneg {n S C q : ℝ} (hn : 0 < n) (hq : 0 < q) (hSC : S ≤ C) (hCq : C ≤ q*n) :
    0 ≤ F n S C q := by
  unfold F; apply div_nonneg
  · apply mul_nonneg <;> linarith
  · positivity

lemma F_pos {n S C q : ℝ} (hn : 0 < n) (hq : 0 < q) (hSC : S ≤ C) (hCq : C < q*n) :
    0 < F n S C q := by
  unfold F; apply div_pos
  · apply mul_pos <;> linarith
  · positivity

lemma Pi_nonneg {n S C q : ℝ} (hn : 0 < n) (hSC : S ≤ C) : 0 ≤ Pi n S C q := by
  unfold Pi; split_ifs with h
  · exact F_nonneg hn h.1 hSC h.2
  · exact le_rfl

lemma Pi_eq {n S C q : ℝ} (hq : 0 < q) (h : C ≤ q*n) : Pi n S C q = F n S C q := by
  unfold Pi; rw [if_pos ⟨hq, h⟩]

lemma Pi_zero {n S C q : ℝ} (h : q*n < C) : Pi n S C q = 0 := by
  unfold Pi; rw [if_neg]; intro h'; linarith [h'.2]

lemma Pi_nonpos_q {n S C q : ℝ} (h : q ≤ 0) : Pi n S C q = 0 := by
  unfold Pi; rw [if_neg]; intro h'; linarith [h'.1]

lemma F_diff_q (n S C q q' : ℝ) (hn : 0 < n) (hq : 0 < q) (hq' : 0 < q') :
    F n S C q' - F n S C q = (q'-q)*(n^2*q*q' - (2*S*C - C^2))/(2*n*q*q') := by
  unfold F; field_simp; ring

lemma F_diff_C (n S C C' q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    F n S C q - F n S C' q = (C'-C)*(C'+C-2*S)/(2*n*q) := by
  unfold F; field_simp; ring

lemma Pi_mono_q {n S C q q' : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC : S ≤ C) (hqq : q ≤ q') :
    Pi n S C q ≤ Pi n S C q' := by
  by_cases h : 0 < q ∧ C ≤ q*n
  · obtain ⟨hq, hC⟩ := h
    have hq' : 0 < q' := by linarith
    have hC' : C ≤ q'*n := by nlinarith
    rw [Pi_eq hq hC, Pi_eq hq' hC']
    have key := F_diff_q n S C q q' hn hq hq'
    have : 0 ≤ (q'-q)*(n^2*q*q' - (2*S*C - C^2))/(2*n*q*q') := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith)
      nlinarith [mul_le_mul hC hC' (by linarith : 0 ≤ C) (by positivity : 0 ≤ q * n)]
    linarith
  · have : Pi n S C q = 0 := by unfold Pi; rw [if_neg h]
    rw [this]; exact Pi_nonneg hn hSC

lemma Pi_strict_q {n S C q q' : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC : S ≤ C) (hqq : q < q')
    (hlt : C < q'*n) : Pi n S C q < Pi n S C q' := by
  have hq' : 0 < q' := by
    by_contra h; push_neg at h; nlinarith
  rw [Pi_eq hq' hlt.le]
  by_cases h : 0 < q ∧ C ≤ q*n
  · obtain ⟨hq, hC⟩ := h
    rw [Pi_eq hq hC]
    have key := F_diff_q n S C q q' hn hq hq'
    have : 0 < (q'-q)*(n^2*q*q' - (2*S*C - C^2))/(2*n*q*q') := by
      apply div_pos _ (by positivity)
      apply mul_pos (by linarith)
      have h1 : C*C ≤ q*n*C := mul_le_mul_of_nonneg_right hC (by linarith)
      have h2 : q*n*C < q*n*(q'*n) := mul_lt_mul_of_pos_left hlt (by positivity)
      nlinarith
    linarith
  · have : Pi n S C q = 0 := by unfold Pi; rw [if_neg h]
    rw [this]; exact F_pos hn hq' hSC hlt

lemma Pi_mono_C {n S C C' q : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC : S ≤ C) (hCC : C ≤ C') :
    Pi n S C' q ≤ Pi n S C q := by
  by_cases h : 0 < q ∧ C' ≤ q*n
  · obtain ⟨hq, hC⟩ := h
    rw [Pi_eq hq hC, Pi_eq hq (by linarith)]
    have key := F_diff_C n S C C' q hn hq
    have : 0 ≤ (C'-C)*(C'+C-2*S)/(2*n*q) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg <;> linarith
    linarith
  · have : Pi n S C' q = 0 := by unfold Pi; rw [if_neg h]
    rw [this]; exact Pi_nonneg hn hSC

lemma Pi_strict_C {n S C C' q : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC : S ≤ C) (hCC : C < C')
    (hlt : C < q*n) : Pi n S C' q < Pi n S C q := by
  have hq : 0 < q := by
    by_contra h; push_neg at h; nlinarith
  rw [Pi_eq hq hlt.le]
  by_cases h : C' ≤ q*n
  · rw [Pi_eq hq h]
    have key := F_diff_C n S C C' q hn hq
    have : 0 < (C'-C)*(C'+C-2*S)/(2*n*q) := by
      apply div_pos _ (by positivity)
      apply mul_pos <;> linarith
    linarith
  · push_neg at h
    rw [Pi_zero h]; exact F_pos hn hq hSC hlt

lemma Pi_le2 {n S C C' q q' : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC' : S ≤ C') (hCC : C' ≤ C)
    (hqq : q ≤ q') : Pi n S C q ≤ Pi n S C' q' :=
  (Pi_mono_q hn hS (by linarith) hqq).trans (Pi_mono_C hn hS hSC' hCC)

lemma Pi_lt2 {n S C C' q q' : ℝ} (hn : 0 < n) (hS : 0 ≤ S) (hSC' : S ≤ C') (hCC : C' ≤ C)
    (hqq : q ≤ q') (hlt : C' < q'*n) (hne : C ≠ C' ∨ q ≠ q') : Pi n S C q < Pi n S C' q' := by
  rcases lt_or_eq_of_le hCC with h | h
  · exact lt_of_le_of_lt (Pi_mono_q hn hS (by linarith) hqq) (Pi_strict_C hn hS hSC' h hlt)
  · rw [← h]
    have hq : q < q' := lt_of_le_of_ne hqq (by
      rcases hne with h' | h'
      · exact absurd h.symm h'
      · exact h')
    exact Pi_strict_q hn hS hSC' hq hlt


section model
variable (P : Params)

noncomputable def Dl (C : ℝ) : ℝ := B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2)
noncomputable def xr (C : ℝ) : ℝ := (B P + Real.sqrt (Dl P C)) / 2
noncomputable def WL : ℝ := Pi P.Nbar P.SL P.SL P.vL

lemma p2_eq (α C : ℝ) : p2 P α C = xr P C / α := by unfold p2 xr Dl; ring
lemma alphaStar_eq : alphaStar P = xr P P.SH / P.vH := by unfold alphaStar xr Dl; ring

lemma B_gt (hP : P.Standing) : 2*P.SL < P.Nbar * B P := by
  obtain ⟨hn, hvL, _, _, _, h6, _⟩ := hP
  have hgap : P.Nbar * B P - 2*P.SL = (P.Nbar*P.vL - P.SL)^2/(P.Nbar*P.vL) := by
    unfold B; field_simp; ring
  have : 0 < (P.Nbar*P.vL - P.SL)^2/(P.Nbar*P.vL) := by
    have : 0 < P.Nbar*P.vL - P.SL := by linarith
    positivity
  linarith

lemma Dl_gap (hP : P.Standing) (C : ℝ) :
    Dl P C - (B P - 2*C/P.Nbar)^2 = 4*C/P.Nbar^2*(P.Nbar * B P - 2*P.SL) := by
  have hn := hP.1
  unfold Dl; field_simp; ring

lemma sqrt_gt_abs (hP : P.Standing) {C : ℝ} (hC : 0 < C) :
    |B P - 2*C/P.Nbar| < Real.sqrt (Dl P C) := by
  have hn := hP.1
  have h1 := Dl_gap P hP C
  have h2 := B_gt P hP
  have h3 : 0 < 4*C/P.Nbar^2*(P.Nbar * B P - 2*P.SL) := by
    apply mul_pos (by positivity) (by linarith)
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs]; linarith

lemma Dl_nonneg (hP : P.Standing) {C : ℝ} (hC : 0 < C) : 0 ≤ Dl P C := by
  have := sqrt_gt_abs P hP hC
  by_contra h; push_neg at h
  rw [Real.sqrt_eq_zero_of_nonpos h.le] at this
  linarith [abs_nonneg (B P - 2*C/P.Nbar)]

lemma xr_gt (hP : P.Standing) {C : ℝ} (hC : 0 < C) : C / P.Nbar < xr P C := by
  have h := sqrt_gt_abs P hP hC
  rw [abs_lt] at h
  unfold xr
  have : 2*C/P.Nbar = 2*(C/P.Nbar) := by ring
  linarith

lemma x1_lt (hP : P.Standing) {C : ℝ} (hC : 0 < C) :
    (B P - Real.sqrt (Dl P C))/2 < C / P.Nbar := by
  have h := sqrt_gt_abs P hP hC
  rw [abs_lt] at h
  have : 2*C/P.Nbar = 2*(C/P.Nbar) := by ring
  linarith

lemma xr_pos (hP : P.Standing) {C : ℝ} (hC : 0 < C) : 0 < xr P C :=
  lt_trans (div_pos hC hP.1) (xr_gt P hP hC)

lemma xr_ge (C : ℝ) : B P / 2 ≤ xr P C := by
  unfold xr; linarith [Real.sqrt_nonneg (Dl P C)]

lemma xr_rel (hP : P.Standing) {C : ℝ} (hC : 0 < C) :
    C^2 - 2*P.SL*C = P.Nbar^2 * (xr P C ^ 2 - B P * xr P C) := by
  have hn := hP.1
  have hs := Real.sq_sqrt (Dl_nonneg P hP hC)
  have h1 : xr P C ^ 2 - B P * xr P C = (Real.sqrt (Dl P C) ^ 2 - B P ^ 2)/4 := by
    unfold xr; ring
  rw [h1, hs]; unfold Dl; field_simp; ring

lemma xr_strict (hP : P.Standing) {C C' : ℝ} (hC : P.SL ≤ C) (hCC : C < C') :
    xr P C < xr P C' := by
  have hn := hP.1
  have hSL := hP.2.2.2.1
  have hC0 : 0 < C := by linarith
  have hD : Dl P C < Dl P C' := by
    unfold Dl
    have : C^2 - 2*P.SL*C < C'^2 - 2*P.SL*C' := by nlinarith
    have : (C^2 - 2*P.SL*C)/P.Nbar^2 < (C'^2 - 2*P.SL*C')/P.Nbar^2 :=
      div_lt_div_of_pos_right this (by positivity)
    linarith
  unfold xr
  have := Real.sqrt_lt_sqrt (Dl_nonneg P hP hC0) hD
  linarith

/-- the quadratic `x² - Bx - K(C)` factors through the two roots. -/
lemma quad_factor (hP : P.Standing) {C : ℝ} (hC : 0 < C) (x : ℝ) :
    x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2 =
      (x - (B P - Real.sqrt (Dl P C))/2) * (x - xr P C) := by
  have hs := Real.sq_sqrt (Dl_nonneg P hP hC)
  unfold xr; unfold Dl at hs ⊢
  linear_combination (1/4 : ℝ) * hs

lemma le_xr_of_quad (hP : P.Standing) {C x : ℝ} (hC : 0 < C)
    (h : x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2 ≤ 0) : x ≤ xr P C := by
  rw [quad_factor P hP hC] at h
  by_contra hx; push_neg at hx
  have h1 : (B P - Real.sqrt (Dl P C))/2 ≤ xr P C := by
    unfold xr; linarith [Real.sqrt_nonneg (Dl P C)]
  have : 0 < (x - (B P - Real.sqrt (Dl P C))/2) * (x - xr P C) :=
    mul_pos (by linarith) (by linarith)
  linarith

lemma quad_of_le_xr (hP : P.Standing) {C x : ℝ} (hC : 0 < C) (h1 : C / P.Nbar ≤ x)
    (h2 : x ≤ xr P C) : x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2 ≤ 0 := by
  rw [quad_factor P hP hC]
  have := x1_lt P hP hC
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

lemma vL_le_xr (hP : P.Standing) {C : ℝ} (hC : P.SL ≤ C) : P.vL ≤ xr P C := by
  have hn := hP.1
  have hvL := hP.2.1
  have hC0 : 0 < C := by linarith [hP.2.2.2.1]
  apply le_xr_of_quad P hP hC0
  have : P.vL^2 - B P * P.vL - (C^2 - 2*P.SL*C)/P.Nbar^2 = -((C - P.SL)^2/P.Nbar^2) := by
    unfold B; field_simp; ring
  rw [this]
  have : 0 ≤ (C - P.SL)^2/P.Nbar^2 := by positivity
  linarith

lemma WL_eq (hP : P.Standing) : WL P = P.Nbar * B P / 2 - P.SL := by
  obtain ⟨hn, hvL, _, _, _, h6, _⟩ := hP
  unfold WL
  rw [Pi_eq hvL (by linarith)]
  unfold F B; field_simp; ring

lemma WL_pos (hP : P.Standing) : 0 < WL P := by
  obtain ⟨hn, hvL, _, hSL, _, h6, _⟩ := hP
  unfold WL
  rw [Pi_eq hvL (by linarith)]
  exact F_pos hn hvL le_rfl (by linarith)

lemma WL_sub_F (hP : P.Standing) {C x : ℝ} (hx : 0 < x) :
    WL P - F P.Nbar P.SL C x =
      -(P.Nbar/(2*x)) * (x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2) := by
  have hn := hP.1
  rw [WL_eq P hP]
  unfold F; field_simp; ring

lemma mimic_le (hP : P.Standing) {C x : ℝ} (hx : 0 < x) (hC : P.SL ≤ C)
    (h : Pi P.Nbar P.SL C x ≤ WL P) : x ≤ xr P C := by
  have hn := hP.1
  have hC0 : 0 < C := by linarith [hP.2.2.2.1]
  by_cases hCx : C ≤ x * P.Nbar
  · rw [Pi_eq hx hCx] at h
    apply le_xr_of_quad P hP hC0
    have e := WL_sub_F P hP (C := C) hx
    have : 0 < P.Nbar/(2*x) := by positivity
    by_contra hq; push_neg at hq
    have : 0 < P.Nbar/(2*x) * (x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2) := mul_pos this hq
    linarith
  · push_neg at hCx
    have h1 := xr_gt P hP hC0
    have : x < C / P.Nbar := by rw [lt_div_iff₀ hn]; linarith
    linarith

lemma mimic_ge (hP : P.Standing) {C x : ℝ} (hx : 0 < x) (hC : P.SL ≤ C)
    (h : x ≤ xr P C) : Pi P.Nbar P.SL C x ≤ WL P := by
  have hn := hP.1
  have hC0 : 0 < C := by linarith [hP.2.2.2.1]
  by_cases hCx : C ≤ x * P.Nbar
  · rw [Pi_eq hx hCx]
    have hq := quad_of_le_xr P hP hC0 (by rw [div_le_iff₀ hn]; linarith) h
    have e := WL_sub_F P hP (C := C) hx
    have : 0 < P.Nbar/(2*x) := by positivity
    have : P.Nbar/(2*x) * (x^2 - B P * x - (C^2 - 2*P.SL*C)/P.Nbar^2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos this.le hq
    linarith
  · push_neg at hCx
    rw [Pi_zero hCx]; exact (WL_pos P hP).le

end model


section opt
variable (P : Params)

lemma alphaStar_pos (hP : P.Standing) : 0 < alphaStar P := by
  rw [alphaStar_eq]
  have := xr_pos P hP (C := P.SH) (by linarith [hP.2.2.2.1, hP.2.2.2.2.1])
  have : 0 < P.vH := by linarith [hP.2.1, hP.2.2.1]
  positivity

lemma caseB (hP : P.Standing) (α : ℝ) (hA : alphaStar P < α) :
    P.SH < Cstar P α ∧ xr P (Cstar P α) = α * P.vH ∧
      0 ≤ P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  have hCs : Cstar P α = P.SL + Real.sqrt (P.SL ^ 2 + P.Nbar ^ 2 *
      (α ^ 2 * P.vH ^ 2 - α * P.vH * B P)) := by
    unfold Cstar; rw [if_neg (not_le.mpr hA)]
  have hxs : xr P P.SH < α * P.vH := by
    rw [alphaStar_eq, div_lt_iff₀ hvH] at hA; exact hA
  have hge := xr_ge P P.SH
  have hrelSH := xr_rel P hP (C := P.SH) (by linarith)
  have hR : (P.SH - P.SL)^2 < P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P) := by
    have h3 : xr P P.SH ^2 - B P * xr P P.SH < α ^ 2 * P.vH ^ 2 - α * P.vH * B P := by
      nlinarith [mul_pos (sub_pos.mpr hxs) (show 0 < α * P.vH + xr P P.SH - B P by linarith)]
    have h4 := mul_lt_mul_of_pos_left h3 (by positivity : (0:ℝ) < P.Nbar^2)
    nlinarith
  set R := P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P) with hRdef
  have hR0 : 0 ≤ R := le_trans (sq_nonneg _) hR.le
  have hsq : P.SH - P.SL < Real.sqrt R := by
    rw [show P.SH - P.SL = Real.sqrt ((P.SH-P.SL)^2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hR
  refine ⟨by rw [hCs]; linarith, ?_, hR0⟩
  have hs := Real.sq_sqrt hR0
  have hK : Cstar P α ^ 2 - 2 * P.SL * Cstar P α =
      P.Nbar^2 * ((α * P.vH)^2 - B P * (α * P.vH)) := by
    rw [hCs]; linear_combination hs
  have hD : Dl P (Cstar P α) = (2 * (α * P.vH) - B P)^2 := by
    unfold Dl; rw [hK]; field_simp; ring
  unfold xr; rw [hD, Real.sqrt_sq (by linarith)]; ring

lemma G_formula (hP : P.Standing) {α x C : ℝ} (hα : 0 < α) (hx : 0 < x)
    (h : C^2 - 2*P.SL*C = P.Nbar^2 * (x^2 - B P * x)) :
    F P.Nbar P.SH C (x/α) = P.Nbar*x*(1/α - α)/2 + P.Nbar*α*B P/2 - P.SH
      + α*(P.SH - P.SL)*(C/x)/P.Nbar := by
  have hn := hP.1
  have e : F P.Nbar P.SH C (x/α) - (P.Nbar*x*(1/α - α)/2 + P.Nbar*α*B P/2 - P.SH
      + α*(P.SH - P.SL)*(C/x)/P.Nbar) =
      -(α/(2*P.Nbar*x)) * (C^2 - 2*P.SL*C - P.Nbar^2 * (x^2 - B P * x)) := by
    unfold F; field_simp; ring
  rw [h, sub_self, mul_zero] at e
  linarith

lemma ratio_lt {n B SL C Cs x xs : ℝ} (hn : 0 < n) (hSL : 0 < SL) (hB : 2*SL < n*B)
    (hC : SL ≤ C) (hCs : SL < Cs) (hx : 0 < x) (hxx : x < xs)
    (hCx : C < n*x) (hCsx : Cs < n*xs)
    (h1 : C^2 - 2*SL*C = n^2*(x^2 - B*x)) (h2 : Cs^2 - 2*SL*Cs = n^2*(xs^2 - B*xs)) :
    C/x < Cs/xs := by
  have hxs : 0 < xs := by linarith
  rw [div_lt_div_iff₀ hx hxs]
  have hE : 0 < (Cs-SL)*x + (C-SL)*xs := by
    have : 0 < (Cs-SL)*x := mul_pos (by linarith) hx
    have : 0 ≤ (C-SL)*xs := mul_nonneg (by linarith) hxs.le
    linarith
  have hDE : ((Cs-SL)*x - (C-SL)*xs) * ((Cs-SL)*x + (C-SL)*xs) =
      (xs-x)*(n^2*B*x*xs - SL^2*(x+xs)) := by
    linear_combination x^2*h2 - xs^2*h1
  have hSE : SL*((Cs-SL)*x + (C-SL)*xs) < n^2*B*x*xs - SL^2*(x+xs) := by
    have e : SL*((Cs-SL)*x + (C-SL)*xs) + SL^2*(x+xs) = SL*(Cs*x + C*xs) := by ring
    have h3 : SL*(Cs*x + C*xs) < SL*(2*n*x*xs) := by
      apply mul_lt_mul_of_pos_left _ hSL
      nlinarith [mul_lt_mul_of_pos_right hCsx hx, mul_lt_mul_of_pos_right hCx hxs]
    have h4 : SL*(2*n*x*xs) < n^2*B*x*xs := by
      have := mul_pos (sub_pos.mpr hB) (mul_pos hn (mul_pos hx hxs))
      nlinarith
    linarith
  have hD : SL*(xs-x) < (Cs-SL)*x - (C-SL)*xs := by
    by_contra hcon; push_neg at hcon
    have : ((Cs-SL)*x - (C-SL)*xs) * ((Cs-SL)*x + (C-SL)*xs) ≤
        SL*(xs-x) * ((Cs-SL)*x + (C-SL)*xs) := mul_le_mul_of_nonneg_right hcon hE.le
    have := mul_lt_mul_of_pos_left hSE (sub_pos.mpr hxx)
    nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
theorem main_opt (hP : P.Standing) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    P.SH ≤ Cstar P α ∧ Cstar P α < P.vH * P.Nbar ∧
    Pi P.Nbar P.SL (Cstar P α) (α * P.vH) ≤ WL P ∧
    (∀ C p, P.SH ≤ C → 0 < p → p ≤ P.vH → (p ≤ P.vL ∨ Pi P.Nbar P.SL C (α*p) ≤ WL P) →
      Pi P.Nbar P.SH C p ≤ Pi P.Nbar P.SH (Cstar P α) P.vH ∧
      (¬(α = 1 ∧ P.SL = P.SH) → (C ≠ Cstar P α ∨ p ≠ P.vH) →
        Pi P.Nbar P.SH C p < Pi P.Nbar P.SH (Cstar P α) P.vH)) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  have hSH0 : 0 ≤ P.SH := by linarith
  by_cases hA : α ≤ alphaStar P
  · have hCs : Cstar P α = P.SH := by unfold Cstar; rw [if_pos hA]
    rw [hCs]
    refine ⟨le_rfl, by linarith [mul_comm P.vH P.Nbar], ?_, ?_⟩
    · rcases eq_or_lt_of_le h0 with h | h
      · rw [← h, zero_mul, Pi_nonpos_q le_rfl]; exact (WL_pos P hP).le
      · apply mimic_ge P hP (by positivity) hSLH
        rw [alphaStar_eq, le_div_iff₀ hvH] at hA; exact hA
    · intro C p hC hp hpv _
      refine ⟨Pi_le2 hn hSH0 le_rfl hC hpv, fun _ hne => Pi_lt2 hn hSH0 le_rfl hC hpv ?_ hne⟩
      linarith [mul_comm P.vH P.Nbar]
  · push_neg at hA
    have hαpos : 0 < α := lt_trans (alphaStar_pos P hP) hA
    obtain ⟨hCsSH, hxrCs, -⟩ := caseB P hP α hA
    set Cs := Cstar P α with hCsdef
    have hCs0 : 0 < Cs := by linarith
    have hCsx : Cs < P.Nbar * (α * P.vH) := by
      have := xr_gt P hP hCs0
      rw [hxrCs, div_lt_iff₀ hn] at this; linarith
    have hCslt : Cs < P.vH * P.Nbar := by nlinarith
    refine ⟨hCsSH.le, hCslt, ?_, ?_⟩
    · exact mimic_ge P hP (by positivity) (by linarith) (by rw [hxrCs])
    · intro C p hC hp hpv hmim
      by_cases hCC : Cs ≤ C
      · exact ⟨Pi_le2 hn hSH0 hCsSH.le hCC hpv,
          fun _ hne => Pi_lt2 hn hSH0 hCsSH.le hCC hpv hCslt hne⟩
      · push_neg at hCC
        have hC0 : 0 < C := by linarith
        have hxC := xr_pos P hP hC0
        have hpx : α * p ≤ xr P C := by
          rcases hmim with h | h
          · have := vL_le_xr P hP (C := C) (by linarith)
            nlinarith
          · exact mimic_le P hP (by positivity) (by linarith) h
        -- value along the frontier
        have hxx : xr P C < xr P Cs := xr_strict P hP (by linarith) hCC
        rw [hxrCs] at hxx
        have hrel1 := xr_rel P hP hC0
        have hrel2 := xr_rel P hP hCs0
        rw [hxrCs] at hrel2
        have hCx : C < P.Nbar * xr P C := by
          have := xr_gt P hP hC0; rw [div_lt_iff₀ hn] at this; linarith
        have hratio : C / xr P C < Cs / (α * P.vH) :=
          ratio_lt hn hSL (B_gt P hP) (by linarith) (by linarith) hxC hxx hCx hCsx hrel1 hrel2
        have hG1 := G_formula P hP hαpos hxC hrel1
        have hG2 := G_formula P hP hαpos (by positivity) hrel2
        have hvHeq : α * P.vH / α = P.vH := by field_simp
        rw [hvHeq] at hG2
        have hle : Pi P.Nbar P.SH C p ≤ Pi P.Nbar P.SH C (xr P C / α) :=
          Pi_mono_q hn hSH0 hC (by rw [le_div_iff₀ hαpos]; linarith)
        have hq1 : C ≤ xr P C / α * P.Nbar := by
          have : xr P C ≤ xr P C / α := by
            rw [le_div_iff₀ hαpos]; nlinarith
          nlinarith
        rw [Pi_eq (by positivity) hq1, hG1] at hle
        rw [Pi_eq hvH hCslt.le, hG2]
        have hinv : α ≤ 1/α := by
          rw [le_div_iff₀ hαpos]; have := mul_le_mul h1 h1 hαpos.le zero_le_one; linarith
        have t1 : 0 ≤ P.Nbar*(α * P.vH - xr P C)*(1/α - α) :=
          mul_nonneg (mul_nonneg hn.le (by linarith)) (by linarith)
        have t2 : 0 ≤ α*(P.SH - P.SL)*(Cs/(α * P.vH) - C/xr P C)/P.Nbar :=
          div_nonneg (mul_nonneg (mul_nonneg hαpos.le (by linarith)) (by linarith)) hn.le
        have hdiff : (P.Nbar * (α * P.vH) * (1 / α - α) / 2 + P.Nbar * α * B P / 2 - P.SH +
            α * (P.SH - P.SL) * (Cs / (α * P.vH)) / P.Nbar) -
            (P.Nbar * xr P C * (1 / α - α) / 2 + P.Nbar * α * B P / 2 - P.SH +
            α * (P.SH - P.SL) * (C / xr P C) / P.Nbar) =
            P.Nbar*(α * P.vH - xr P C)*(1/α - α)/2 +
              α*(P.SH - P.SL)*(Cs/(α * P.vH) - C/xr P C)/P.Nbar := by ring
        refine ⟨by linarith, fun hex _ => ?_⟩
        have : 0 < P.Nbar*(α * P.vH - xr P C)*(1/α - α) ∨
            0 < α*(P.SH - P.SL)*(Cs/(α * P.vH) - C/xr P C)/P.Nbar := by
          by_cases hα1 : α = 1
          · right
            have : P.SL < P.SH := lt_of_le_of_ne hSLH (fun h => hex ⟨hα1, h⟩)
            apply div_pos (mul_pos (mul_pos hαpos (by linarith)) (by linarith)) hn
          · left
            have hlt : α < 1 := lt_of_le_of_ne h1 hα1
            have : α < 1/α := by
              rw [lt_div_iff₀ hαpos]; have := mul_lt_mul_of_pos_left hlt hαpos; linarith
            exact mul_pos (mul_pos hn (by linarith)) (by linarith)
        rcases this with h | h <;> linarith

lemma informed (hP : P.Standing) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (C q : ℝ)
    (hC : P.SH ≤ C) (hq : q ≤ (1 - α) * P.vH) :
    Pi P.Nbar P.SH C q ≤ Pi P.Nbar P.SH (Cstar P α) P.vH := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  have hSH0 : 0 ≤ P.SH := by linarith
  have step : Pi P.Nbar P.SH C q ≤ Pi P.Nbar P.SH P.SH ((1 - α) * P.vH) :=
    Pi_le2 hn hSH0 le_rfl hC hq
  refine step.trans ?_
  by_cases hA : α ≤ alphaStar P
  · have hCs : Cstar P α = P.SH := by unfold Cstar; rw [if_pos hA]
    rw [hCs]; exact Pi_mono_q hn hSH0 le_rfl (by nlinarith)
  · push_neg at hA
    obtain ⟨hCsSH, hxrCs, -⟩ := caseB P hP α hA
    have hCs0 : 0 < Cstar P α := by linarith
    have hCsx : Cstar P α < P.Nbar * (α * P.vH) := by
      have := xr_gt P hP hCs0
      rw [hxrCs, div_lt_iff₀ hn] at this; linarith
    have hCslt : Cstar P α < P.vH * P.Nbar := by nlinarith
    by_cases hw : 0 < (1 - α) * P.vH ∧ P.SH ≤ (1 - α) * P.vH * P.Nbar
    · obtain ⟨hw0, hw1⟩ := hw
      rw [Pi_eq hw0 hw1, Pi_eq hvH hCslt.le]
      unfold F
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      set W := (1 - α) * P.vH * P.Nbar with hW
      set X := α * P.vH * P.Nbar with hX
      set a := P.SH
      set Cs := Cstar P α
      have hV : P.vH * P.Nbar = W + X := by rw [hW, hX]; ring
      have hXa : Cs < X := by rw [hX]; linarith
      have hCsq : (Cs - a)^2 ≤ (X - a)^2 := by nlinarith
      have key : (W - a)^2 * (W + X) ≤ ((W + X - a)^2 - (X - a)^2) * W := by
        have e : ((W + X - a)^2 - (X - a)^2) * W - (W - a)^2 * (W + X) =
            W*(W*X - a^2) + a*X*(2*W - a) := by ring
        have : 0 ≤ W*(W*X - a^2) := mul_nonneg (by linarith) (by nlinarith)
        have : 0 ≤ a*X*(2*W - a) := mul_nonneg (mul_nonneg hSH0 (by linarith)) (by linarith)
        linarith
      have e1 : ((1 - α) * P.vH * P.Nbar - a) * ((1 - α) * P.vH * P.Nbar + a - 2 * a) =
          (W - a)^2 := by rw [hW]; ring
      have e2 : (P.vH * P.Nbar - Cs) * (P.vH * P.Nbar + Cs - 2 * a) =
          (W + X - a)^2 - (Cs - a)^2 := by rw [hV]; ring
      rw [e1, e2]
      have hW0 : 0 < W := by rw [hW]; positivity
      have : (W - a)^2 * (2 * P.Nbar * P.vH) ≤
          ((W + X - a)^2 - (Cs - a)^2) * (2 * P.Nbar * ((1 - α) * P.vH)) := by
        have hNv : 2 * P.Nbar * P.vH = 2 * (W + X) := by rw [← hV]; ring
        have hNw : 2 * P.Nbar * ((1 - α) * P.vH) = 2 * W := by rw [hW]; ring
        rw [hNv, hNw]; nlinarith
      exact this
    · have : Pi P.Nbar P.SH P.SH ((1 - α) * P.vH) = 0 := by unfold Pi; rw [if_neg hw]
      rw [this]; exact Pi_nonneg hn hCsSH.le

end opt


section prof
variable (P : Params)

lemma prof_eq (hn : 0 < P.Nbar) (α : ℝ) (tru bel : CType) (C p : ℝ) (hC : 0 < C) :
    profit P α tru bel ⟨C, p⟩ = Pi P.Nbar (cost P tru) C (demandFrac P α tru bel p * p) := by
  unfold profit; exact cp_eq P hn _ _ _ _ hC

lemma dHH_le (α p : ℝ) (h : p ≤ P.vH) : demandFrac P α .H .H p = 1 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dHH_gt (α p : ℝ) (h : P.vH < p) : demandFrac P α .H .H p = 0 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dLL_le (α p : ℝ) (h : p ≤ P.vL) : demandFrac P α .L .L p = 1 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dLL_gt (α p : ℝ) (h : P.vL < p) : demandFrac P α .L .L p = 0 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dLH_le (α p : ℝ) (h : p ≤ P.vL) (h' : p ≤ P.vH) : demandFrac P α .L .H p = 1 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dLH_mid (α p : ℝ) (h : P.vL < p) (h' : p ≤ P.vH) : demandFrac P α .L .H p = α := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dLH_gt (α p : ℝ) (h : P.vL < p) (h' : P.vH < p) : demandFrac P α .L .H p = 0 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dHL_le (α p : ℝ) (h : p ≤ P.vL) (h' : p ≤ P.vH) : demandFrac P α .H .L p = 1 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dHL_mid (α p : ℝ) (h : P.vL < p) (h' : p ≤ P.vH) : demandFrac P α .H .L p = 1 - α := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)
lemma dHL_gt (α p : ℝ) (h : P.vL < p) (h' : P.vH < p) : demandFrac P α .H .L p = 0 := by
  unfold demandFrac; split_ifs <;> simp only [val] at * <;> first | ring1 | (exfalso; linarith)

end prof

set_option maxHeartbeats 1000000 in
theorem prop3 (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsSepEq P α ⟨P.SL, P.vL⟩ ⟨Cstar P α, P.vH⟩ ∧
    SurvivesIC P α ⟨P.SL, P.vL⟩ ⟨Cstar P α, P.vH⟩ ∧
    ∀ dL dH : Design, IsSepEq P α dL dH → SurvivesIC P α dL dH →
      dL = ⟨P.SL, P.vL⟩ ∧
      (¬ (α = 1 ∧ P.SL = P.SH) → dH = ⟨Cstar P α, P.vH⟩) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  have hSH0 : 0 ≤ P.SH := by linarith
  obtain ⟨hCs1, hCs2, hCs3, hopt⟩ := main_opt P hP α hα0 hα1
  set Cs := Cstar P α with hCsdef
  have hCs0 : 0 < Cs := by linarith
  have hWLpos := WL_pos P hP
  set Vs := Pi P.Nbar P.SH Cs P.vH with hVsdef
  have hVspos : 0 < Vs := by
    rw [hVsdef, Pi_eq hvH hCs2.le]; exact F_pos hn hvH hCs1 hCs2
  have hWL : profit P α .L .L ⟨P.SL, P.vL⟩ = WL P := by
    rw [prof_eq P hn α _ _ _ _ hSL, dLL_le P α _ le_rfl, one_mul]; rfl
  have hVs : profit P α .H .H ⟨Cs, P.vH⟩ = Vs := by
    rw [prof_eq P hn α _ _ _ _ hCs0, dHH_le P α _ le_rfl, one_mul]; rfl
  -- L optimum
  have hLopt : ∀ d : Design, Feasible P .L d →
      profit P α .L .L d ≤ WL P ∧ (d ≠ ⟨P.SL, P.vL⟩ → profit P α .L .L d < WL P) := by
    rintro ⟨C, p⟩ hf
    simp only [Feasible, cost] at hf
    obtain ⟨hC, hp⟩ := hf
    have hC0 : 0 < C := by linarith
    rw [prof_eq P hn α _ _ _ _ hC0]
    by_cases hpv : p ≤ P.vL
    · rw [dLL_le P α _ hpv, one_mul]
      refine ⟨Pi_le2 hn hSL.le le_rfl hC hpv, fun hne => ?_⟩
      apply Pi_lt2 hn hSL.le le_rfl hC hpv (by linarith [mul_comm P.vL P.Nbar])
      by_contra hcon; push_neg at hcon; exact hne (by rw [hcon.1, hcon.2])
    · push_neg at hpv
      rw [dLL_gt P α _ hpv, zero_mul, Pi_nonpos_q le_rfl]
      exact ⟨hWLpos.le, fun _ => hWLpos⟩
  -- H constrained optimum
  have hHopt : ∀ d : Design, Feasible P .H d → profit P α .L .H d ≤ WL P →
      profit P α .H .H d ≤ Vs ∧
      (¬(α = 1 ∧ P.SL = P.SH) → d ≠ ⟨Cs, P.vH⟩ → profit P α .H .H d < Vs) := by
    rintro ⟨C, p⟩ hf hm
    simp only [Feasible, cost] at hf
    obtain ⟨hC, hp⟩ := hf
    have hC0 : 0 < C := by linarith
    rw [prof_eq P hn α _ _ _ _ hC0]
    by_cases hpv : p ≤ P.vH
    · rw [dHH_le P α _ hpv, one_mul]
      have hm' : p ≤ P.vL ∨ Pi P.Nbar P.SL C (α*p) ≤ WL P := by
        by_cases hpl : p ≤ P.vL
        · exact Or.inl hpl
        · push_neg at hpl
          right
          rw [prof_eq P hn α _ _ _ _ hC0, dLH_mid P α _ hpl hpv] at hm
          exact hm
      obtain ⟨h1, h2⟩ := hopt C p hC hp hpv hm'
      refine ⟨h1, fun hex hne => h2 hex ?_⟩
      by_contra hcon; push_neg at hcon; exact hne (by rw [hcon.1, hcon.2])
    · push_neg at hpv
      rw [dHH_gt P α _ hpv, zero_mul, Pi_nonpos_q le_rfl]
      exact ⟨hVspos.le, fun _ _ => hVspos⟩
  -- deviations of H when believed L
  have hHL : ∀ d : Design, Feasible P .H d → profit P α .H .L d ≤ Vs := by
    rintro ⟨C, p⟩ hf
    have hf' := hf
    simp only [Feasible, cost] at hf
    obtain ⟨hC, hp⟩ := hf
    have hC0 : 0 < C := by linarith
    by_cases hpl : p ≤ P.vL
    · have hpv : p ≤ P.vH := by linarith
      have e1 : profit P α .H .L ⟨C, p⟩ = profit P α .H .H ⟨C, p⟩ := by
        rw [prof_eq P hn α _ _ _ _ hC0, prof_eq P hn α _ _ _ _ hC0, dHL_le P α _ hpl hpv,
          dHH_le P α _ hpv]
      rw [e1]
      apply (hHopt _ hf' _).1
      rw [prof_eq P hn α _ _ _ _ hC0, dLH_le P α _ hpl hpv, one_mul]
      exact Pi_le2 hn hSL.le le_rfl (by linarith) hpl
    · push_neg at hpl
      rw [prof_eq P hn α _ _ _ _ hC0]
      by_cases hpv : p ≤ P.vH
      · rw [dHL_mid P α _ hpl hpv]
        exact informed P hP α hα0 hα1 C _ hC (by nlinarith)
      · push_neg at hpv
        rw [dHL_gt P α _ hpl hpv, zero_mul, Pi_nonpos_q le_rfl]; exact hVspos.le
  have hmim : profit P α .L .H ⟨Cs, P.vH⟩ ≤ WL P := by
    rw [prof_eq P hn α _ _ _ _ hCs0, dLH_mid P α _ hvLH le_rfl]; exact hCs3
  have hEq : IsSepEq P α ⟨P.SL, P.vL⟩ ⟨Cs, P.vH⟩ := by
    refine ⟨⟨⟨le_refl _, hvL⟩, ⟨hCs1, hvH⟩, fun h => ?_⟩, ⟨fun d hd _ => ?_, ?_⟩,
      fun d hd _ => ?_⟩
    · have := congrArg Design.p h; simp at this; linarith
    · rw [hWL]; exact (hLopt d hd).1
    · rw [hWL]; exact hmim
    · rw [hVs]; exact hHL d hd
  have hIC : SurvivesIC P α ⟨P.SL, P.vL⟩ ⟨Cs, P.vH⟩ := by
    rintro ⟨d, _, _, (⟨hf, hgt, hlt1, _⟩ | ⟨hf, hgt, _⟩)⟩
    · rw [hWL] at hlt1; rw [hVs] at hgt
      have := (hHopt d hf hlt1.le).1; linarith
    · rw [hWL] at hgt; linarith [(hLopt d hf).1]
  refine ⟨hEq, hIC, ?_⟩
  intro dL dH hE hS
  obtain ⟨⟨hfL, hfH, hne⟩, ⟨hLall, hLmim⟩, hHall⟩ := hE
  have hdL : dL = ⟨P.SL, P.vL⟩ := by
    by_contra hcon
    have h1 := (hLopt dL hfL).2 hcon
    by_cases hdH : (⟨P.SL, P.vL⟩ : Design) = dH
    · have : profit P α .L .H dH = WL P := by
        rw [← hdH, prof_eq P hn α _ _ _ _ hSL, dLH_le P α _ le_rfl hvLH.le, one_mul]; rfl
      linarith
    · have := hLall ⟨P.SL, P.vL⟩ ⟨le_refl _, hvL⟩ hdH
      rw [hWL] at this; linarith
  refine ⟨hdL, fun hexc => ?_⟩
  subst hdL
  rw [hWL] at hLmim
  obtain ⟨hle, hlt⟩ := hHopt dH hfH hLmim
  by_contra hne'
  have hV0 := hlt hexc hne'
  set V0 := profit P α .H .H dH with hV0def
  set δ := min ((P.vH * P.Nbar - Cs)/2) ((Vs - V0)/2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (P.vH * P.Nbar - Cs)/2 := min_le_left _ _
  have hδ2 : δ ≤ (Vs - V0)/2 := min_le_right _ _
  have hCd0 : 0 < Cs + δ := by linarith
  have hVd : V0 < profit P α .H .H ⟨Cs + δ, P.vH⟩ := by
    rw [prof_eq P hn α _ _ _ _ hCd0, dHH_le P α _ le_rfl, one_mul]
    simp only [cost]
    rw [Pi_eq hvH (by linarith)]
    have e := F_diff_C P.Nbar P.SH Cs (Cs + δ) P.vH hn hvH
    have hVs' : Vs = F P.Nbar P.SH Cs P.vH := by rw [hVsdef, Pi_eq hvH hCs2.le]
    have hb : (Cs + δ - Cs) * (Cs + δ + Cs - 2 * P.SH) / (2 * P.Nbar * P.vH) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      have : Cs + δ + Cs - 2 * P.SH ≤ 2 * P.Nbar * P.vH := by nlinarith
      have h2 : (Cs + δ - Cs) = δ := by ring
      rw [h2]; nlinarith
    linarith
  apply hS
  refine ⟨⟨Cs + δ, P.vH⟩, ?_, ?_, Or.inl ⟨⟨by simp only [cost]; linarith, hvH⟩, hVd, ?_, ?_⟩⟩
  · intro h; have := congrArg Design.p h; simp at this; linarith
  · intro h; rw [h] at hVd; exact lt_irrefl _ hVd
  · rw [hWL, prof_eq P hn α _ _ _ _ hCd0, dLH_mid P α _ hvLH le_rfl]
    simp only [cost]
    rcases eq_or_lt_of_le hα0 with h | h
    · rw [← h, zero_mul, Pi_nonpos_q le_rfl]; exact hWLpos
    · by_cases hc : Cs < α * P.vH * P.Nbar
      · exact lt_of_lt_of_le (Pi_strict_C hn hSL.le (by linarith) (by linarith) hc) hCs3
      · push_neg at hc
        rw [Pi_zero (by linarith)]; exact hWLpos
  · rw [hWL, prof_eq P hn α _ _ _ _ hCd0, dLL_gt P α _ hvLH, zero_mul, Pi_nonpos_q le_rfl]
    exact hWLpos


/-! ## Milestones -/

lemma ms_prop1 (P : Params) (hP : P.Standing) (i : CType) :
    (∀ d : Design, cost P i ≤ d.C → 0 < d.p → d.p ≤ val P i →
      campaignProfit P 1 (cost P i) d.C d.p ≤
        campaignProfit P 1 (cost P i) (cost P i) (val P i)) ∧
    (∀ d : Design, cost P i ≤ d.C → 0 < d.p → d.p ≤ val P i →
      campaignProfit P 1 (cost P i) d.C d.p =
        campaignProfit P 1 (cost P i) (cost P i) (val P i) →
      d = ⟨cost P i, val P i⟩) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hc0 : 0 < cost P i := by cases i <;> simp only [cost] <;> linarith
  have hcv : cost P i < val P i * P.Nbar := by
    cases i <;> simp only [cost, val] <;> linarith [mul_comm P.vH P.Nbar, mul_comm P.vL P.Nbar]
  constructor
  · rintro ⟨C, p⟩ hC hp hpv
    simp only at hC hp hpv
    rw [cp_eq P hn _ _ _ _ (by linarith), cp_eq P hn _ _ _ _ hc0, one_mul, one_mul]
    exact Pi_le2 hn hc0.le le_rfl hC hpv
  · rintro ⟨C, p⟩ hC hp hpv heq
    simp only at hC hp hpv heq
    rw [cp_eq P hn _ _ _ _ (by linarith), cp_eq P hn _ _ _ _ hc0, one_mul, one_mul] at heq
    by_contra hne
    have : C ≠ cost P i ∨ p ≠ val P i := by
      by_contra h; push_neg at h; exact hne (by rw [h.1, h.2])
    have := Pi_lt2 hn hc0.le le_rfl hC hpv hcv this
    linarith

lemma ms_prop1_sep (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (dL dH : Design) (h : IsSepEq P α dL dH) :
    dL = ⟨P.SL, P.vL⟩ := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hWLpos := WL_pos P hP
  have hWL : profit P α .L .L ⟨P.SL, P.vL⟩ = WL P := by
    rw [prof_eq P hn α _ _ _ _ hSL, dLL_le P α _ le_rfl, one_mul]; rfl
  have hLopt : ∀ d : Design, Feasible P .L d →
      profit P α .L .L d ≤ WL P ∧ (d ≠ ⟨P.SL, P.vL⟩ → profit P α .L .L d < WL P) := by
    rintro ⟨C, p⟩ hf
    simp only [Feasible, cost] at hf
    obtain ⟨hC, hp⟩ := hf
    have hC0 : 0 < C := by linarith
    rw [prof_eq P hn α _ _ _ _ hC0]
    by_cases hpv : p ≤ P.vL
    · rw [dLL_le P α _ hpv, one_mul]
      refine ⟨Pi_le2 hn hSL.le le_rfl hC hpv, fun hne => ?_⟩
      apply Pi_lt2 hn hSL.le le_rfl hC hpv (by linarith [mul_comm P.vL P.Nbar])
      by_contra hcon; push_neg at hcon; exact hne (by rw [hcon.1, hcon.2])
    · push_neg at hpv
      rw [dLL_gt P α _ hpv, zero_mul, Pi_nonpos_q le_rfl]
      exact ⟨hWLpos.le, fun _ => hWLpos⟩
  obtain ⟨⟨hfL, hfH, hne⟩, ⟨hLall, hLmim⟩, _⟩ := h
  by_contra hcon
  have h1 := (hLopt dL hfL).2 hcon
  by_cases hdH : (⟨P.SL, P.vL⟩ : Design) = dH
  · have : profit P α .L .H dH = WL P := by
      rw [← hdH, prof_eq P hn α _ _ _ _ hSL, dLH_le P α _ le_rfl hvLH.le, one_mul]; rfl
    linarith
  · have := hLall ⟨P.SL, P.vL⟩ ⟨le_refl _, hvL⟩ hdH
    rw [hWL] at this; linarith

lemma ms_closed (P : Params) (hP : P.Standing) (k S C p : ℝ) :
    (0 < k → 0 < p → 0 ≤ C → C < k * p * P.Nbar →
      campaignProfit P k S C p =
        P.Nbar / 2 * (k * p) + (2 * S * C - C ^ 2) / (2 * P.Nbar * (k * p)) - S) ∧
    (0 < C → k * p * P.Nbar ≤ C → campaignProfit P k S C p = 0) := by
  have hn := hP.1
  constructor
  · intro hk hp hC hlt
    have hq : 0 < k * p := mul_pos hk hp
    unfold campaignProfit
    have hset : Set.Icc 0 P.Nbar ∩ {N : ℝ | C ≤ k * p * N} = Set.Icc (C/(k*p)) P.Nbar := by
      ext N
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq]
      rw [div_le_iff₀ hq]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by linarith, h1⟩
      · rintro ⟨h2, h1⟩
        refine ⟨⟨?_, h1⟩, by linarith⟩
        by_contra hneg; push_neg at hneg; nlinarith
    have hab : C/(k*p) ≤ P.Nbar := by rw [div_le_iff₀ hq]; linarith
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    have hk' : k ≠ 0 := hk.ne'
    have hp' : p ≠ 0 := hp.ne'
    field_simp; ring
  · intro hC hle
    rw [cp_eq P hn _ _ _ _ hC]
    by_cases hq : 0 < k * p
    · rcases lt_or_eq_of_le hle with h | h
      · exact Pi_zero h
      · rw [Pi_eq hq h.ge]; unfold F; rw [h]; simp
    · push_neg at hq; exact Pi_nonpos_q hq

lemma ms_mimic_iff (P : Params) (hP : P.Standing) (α C p : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : P.SH ≤ C) (hpL : P.vL < p) (hpH : p ≤ P.vH) (hsucc : C < α * p * P.Nbar) :
    profit P α .L .H ⟨C, p⟩ ≤ profit P α .L .L ⟨P.SL, P.vL⟩ ↔
      p1 P α C ≤ p ∧ p ≤ p2 P α C := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hC0 : 0 < C := by linarith
  have hWL : profit P α .L .L ⟨P.SL, P.vL⟩ = WL P := by
    rw [prof_eq P hn α _ _ _ _ hSL, dLL_le P α _ le_rfl, one_mul]; rfl
  rw [hWL, prof_eq P hn α _ _ _ _ hC0, dLH_mid P α _ hpL hpH]
  simp only [cost]
  have hp0 : 0 < p := by linarith
  have hx1 := x1_lt P hP hC0
  have hp1 : p1 P α C ≤ p := by
    have : p1 P α C = (B P - Real.sqrt (Dl P C))/2/α := by unfold p1 Dl; ring
    rw [this, div_le_iff₀ hα0]
    have : C / P.Nbar < α * p := by rw [div_lt_iff₀ hn]; linarith
    linarith
  rw [p2_eq, le_div_iff₀ hα0]
  constructor
  · intro h; exact ⟨hp1, by have := mimic_le P hP (by positivity) (by linarith) h; linarith⟩
  · rintro ⟨_, h⟩; exact mimic_ge P hP (by positivity) (by linarith) (by linarith)

lemma ms_eq8 (P : Params) (hP : P.Standing) (α C : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : P.SH ≤ C) :
    |B P - 2 * (C / P.Nbar)| <
        Real.sqrt (B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2)) ∧
      p1 P α C < C / (α * P.Nbar) ∧ C / (α * P.Nbar) < p2 P α C ∧
      C / P.Nbar ≤ C / (α * P.Nbar) := by
  have hn := hP.1
  have hC0 : 0 < C := by linarith [hP.2.2.2.1, hP.2.2.2.2.1]
  have h1 := sqrt_gt_abs P hP hC0
  have e : 2 * C / P.Nbar = 2 * (C / P.Nbar) := by ring
  rw [e] at h1
  have hx1 := x1_lt P hP hC0
  have hx2 := xr_gt P hP hC0
  have eC : C / (α * P.Nbar) = (C / P.Nbar) / α := by field_simp
  refine ⟨h1, ?_, ?_, ?_⟩
  · have : p1 P α C = (B P - Real.sqrt (Dl P C))/2/α := by unfold p1 Dl; ring
    rw [this, eC]; exact div_lt_div_of_pos_right hx1 hα0
  · rw [p2_eq, eC]; exact div_lt_div_of_pos_right hx2 hα0
  · rw [eC, le_div_iff₀ hα0]
    have : 0 < C / P.Nbar := by positivity
    nlinarith

lemma ms_case1 (P : Params) (hP : P.Standing) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (P.vH ≤ p2 P α P.SH ↔ α ≤ alphaStar P) ∧
    (α ≤ alphaStar P →
      profit P α .L .H ⟨P.SH, P.vH⟩ ≤ profit P α .L .L ⟨P.SL, P.vL⟩) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  constructor
  · rw [p2_eq, alphaStar_eq, le_div_iff₀ hα0, le_div_iff₀ hvH, mul_comm]
  · intro hA
    have hCs : Cstar P α = P.SH := by unfold Cstar; rw [if_pos hA]
    obtain ⟨_, _, h3, _⟩ := main_opt P hP α hα0.le hα1
    rw [hCs] at h3
    have hWL : profit P α .L .L ⟨P.SL, P.vL⟩ = WL P := by
      rw [prof_eq P hn α _ _ _ _ hSL, dLL_le P α _ le_rfl, one_mul]; rfl
    rw [hWL, prof_eq P hn α _ _ _ _ (by linarith), dLH_mid P α _ hvLH le_rfl]
    exact h3

lemma ms_case2 (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    0 ≤ P.SL ^ 2 + P.Nbar ^ 2 * (α ^ 2 * P.vH ^ 2 - α * P.vH * B P) ∧
      P.SH < Cstar P α ∧ p2 P α (Cstar P α) = P.vH ∧
      ∀ C : ℝ, P.SH ≤ C → p2 P α C = P.vH → C = Cstar P α := by
  have hSLH := hP.2.2.2.2.1
  have hαpos : 0 < α := lt_trans (alphaStar_pos P hP) hα
  obtain ⟨h1, h2, h3⟩ := caseB P hP α hα
  refine ⟨h3, h1, by rw [p2_eq, h2]; field_simp, fun C hC hp => ?_⟩
  rw [p2_eq, div_eq_iff hαpos.ne'] at hp
  have hx : xr P C = xr P (Cstar P α) := by rw [h2, hp]; ring
  rcases lt_trichotomy C (Cstar P α) with h | h | h
  · have := xr_strict P hP (by linarith) h; linarith
  · exact h
  · have := xr_strict P hP (by linarith) h; linarith

/-- frontier comparison: for `S_H ≤ C₁ < C₂`, the H-profit along `p = p₂(C)` increases. -/
lemma frontier (P : Params) (hP : P.Standing) (α : ℝ) (hαpos : 0 < α) (hα1 : α ≤ 1)
    (C1 C2 : ℝ) (hC1 : P.SH ≤ C1) (hC12 : C1 < C2) :
    F P.Nbar P.SH C1 (xr P C1 / α) ≤ F P.Nbar P.SH C2 (xr P C2 / α) ∧
    (¬(α = 1 ∧ P.SL = P.SH) →
      F P.Nbar P.SH C1 (xr P C1 / α) < F P.Nbar P.SH C2 (xr P C2 / α)) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hC10 : 0 < C1 := by linarith
  have hC20 : 0 < C2 := by linarith
  have hx1 := xr_pos P hP hC10
  have hxx : xr P C1 < xr P C2 := xr_strict P hP (by linarith) hC12
  have hrel1 := xr_rel P hP hC10
  have hrel2 := xr_rel P hP hC20
  have hCx1 : C1 < P.Nbar * xr P C1 := by
    have := xr_gt P hP hC10; rw [div_lt_iff₀ hn] at this; linarith
  have hCx2 : C2 < P.Nbar * xr P C2 := by
    have := xr_gt P hP hC20; rw [div_lt_iff₀ hn] at this; linarith
  have hratio : C1 / xr P C1 < C2 / xr P C2 :=
    ratio_lt hn hSL (B_gt P hP) (by linarith) (by linarith) hx1 hxx hCx1 hCx2 hrel1 hrel2
  rw [G_formula P hP hαpos hx1 hrel1, G_formula P hP hαpos (by linarith) hrel2]
  have hinv : α ≤ 1/α := by
    rw [le_div_iff₀ hαpos]; have := mul_le_mul hα1 hα1 hαpos.le zero_le_one; linarith
  have t1 : 0 ≤ P.Nbar*(xr P C2 - xr P C1)*(1/α - α) :=
    mul_nonneg (mul_nonneg hn.le (by linarith)) (by linarith)
  have t2 : 0 ≤ α*(P.SH - P.SL)*(C2/xr P C2 - C1/xr P C1)/P.Nbar :=
    div_nonneg (mul_nonneg (mul_nonneg hαpos.le (by linarith)) (by linarith)) hn.le
  have hdiff : (P.Nbar * xr P C2 * (1 / α - α) / 2 + P.Nbar * α * B P / 2 - P.SH +
      α * (P.SH - P.SL) * (C2 / xr P C2) / P.Nbar) -
      (P.Nbar * xr P C1 * (1 / α - α) / 2 + P.Nbar * α * B P / 2 - P.SH +
      α * (P.SH - P.SL) * (C1 / xr P C1) / P.Nbar) =
      P.Nbar*(xr P C2 - xr P C1)*(1/α - α)/2 +
        α*(P.SH - P.SL)*(C2/xr P C2 - C1/xr P C1)/P.Nbar := by ring
  refine ⟨by linarith, fun hex => ?_⟩
  have : 0 < P.Nbar*(xr P C2 - xr P C1)*(1/α - α) ∨
      0 < α*(P.SH - P.SL)*(C2/xr P C2 - C1/xr P C1)/P.Nbar := by
    by_cases hα1' : α = 1
    · right
      have : P.SL < P.SH := lt_of_le_of_ne hSLH (fun h => hex ⟨hα1', h⟩)
      apply div_pos (mul_pos (mul_pos hαpos (by linarith)) (by linarith)) hn
    · left
      have hlt : α < 1 := lt_of_le_of_ne hα1 hα1'
      have : α < 1/α := by
        rw [lt_div_iff₀ hαpos]; have := mul_lt_mul_of_pos_left hlt hαpos; linarith
      exact mul_pos (mul_pos hn (by linarith)) (by linarith)
  rcases this with h | h <;> linarith

lemma ms_p2_mono (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    MonotoneOn (fun C => profit P α .H .H ⟨C, p2 P α C⟩) (Set.Icc P.SH (Cstar P α)) ∧
    (¬ (α = 1 ∧ P.SL = P.SH) →
      StrictMonoOn (fun C => profit P α .H .H ⟨C, p2 P α C⟩) (Set.Icc P.SH (Cstar P α))) := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hαpos : 0 < α := lt_trans (alphaStar_pos P hP) hα
  obtain ⟨_, h2, _⟩ := caseB P hP α hα
  -- on the interval, the profit is F along the frontier
  have hval : ∀ C ∈ Set.Icc P.SH (Cstar P α),
      profit P α .H .H ⟨C, p2 P α C⟩ = F P.Nbar P.SH C (xr P C / α) := by
    intro C hC
    obtain ⟨hC1, hC2⟩ := hC
    have hC0 : 0 < C := by linarith
    have hxle : xr P C ≤ α * P.vH := by
      rcases lt_or_eq_of_le hC2 with h | h
      · have := xr_strict P hP (by linarith) h; linarith
      · rw [h, h2]
    have hp2 : p2 P α C ≤ P.vH := by
      rw [p2_eq, div_le_iff₀ hαpos]; linarith
    rw [prof_eq P hn α _ _ _ _ hC0, dHH_le P α _ hp2, one_mul, p2_eq]
    simp only [cost]
    have hx := xr_pos P hP hC0
    have hq1 : C ≤ xr P C / α * P.Nbar := by
      have h1 : xr P C ≤ xr P C / α := by
        rw [le_div_iff₀ hαpos]; nlinarith
      have := xr_gt P hP hC0; rw [div_lt_iff₀ hn] at this
      nlinarith
    exact Pi_eq (by positivity) hq1
  constructor
  · intro a ha b hb hab
    simp only
    rw [hval a ha, hval b hb]
    rcases lt_or_eq_of_le hab with h | h
    · exact (frontier P hP α hαpos hα1 a b ha.1 h).1
    · rw [h]
  · intro hex a ha b hb hab
    simp only
    rw [hval a ha, hval b hb]
    exact (frontier P hP α hαpos hα1 a b ha.1 hab).2 hex

lemma ms_informed (P : Params) (hP : P.Standing) (α : ℝ) (hα : alphaStar P < α)
    (hα1 : α ≤ 1) :
    profit P α .H .L ⟨P.SH, P.vH⟩ < profit P α .H .H ⟨Cstar P α, P.vH⟩ := by
  have hP' := hP
  obtain ⟨hn, hvL, hvLH, hSL, hSLH, hSLn, hSHn⟩ := hP'
  have hvH : 0 < P.vH := by linarith
  have hSH0 : 0 ≤ P.SH := by linarith
  have hαpos : 0 < α := lt_trans (alphaStar_pos P hP) hα
  obtain ⟨hCsSH, hxrCs, _⟩ := caseB P hP α hα
  have hCs0 : 0 < Cstar P α := by linarith
  have hCsx : Cstar P α < P.Nbar * (α * P.vH) := by
    have := xr_gt P hP hCs0
    rw [hxrCs, div_lt_iff₀ hn] at this; linarith
  have hCslt : Cstar P α < P.vH * P.Nbar := by nlinarith
  rw [prof_eq P hn α _ _ _ _ (by linarith), dHL_mid P α _ hvLH le_rfl,
    prof_eq P hn α _ _ _ _ hCs0, dHH_le P α _ le_rfl, one_mul]
  simp only [cost]
  have hVpos : 0 < Pi P.Nbar P.SH (Cstar P α) P.vH := by
    rw [Pi_eq hvH hCslt.le]; exact F_pos hn hvH hCsSH.le hCslt
  by_cases hw : 0 < (1 - α) * P.vH ∧ P.SH ≤ (1 - α) * P.vH * P.Nbar
  · obtain ⟨hw0, hw1⟩ := hw
    rw [Pi_eq hw0 hw1, Pi_eq hvH hCslt.le]
    unfold F
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    set W := (1 - α) * P.vH * P.Nbar with hW
    set X := α * P.vH * P.Nbar with hX
    set a := P.SH
    set Cs := Cstar P α
    have hV : P.vH * P.Nbar = W + X := by rw [hW, hX]; ring
    have hXa : Cs < X := by rw [hX]; linarith
    have hCsq : (Cs - a)^2 < (X - a)^2 := by nlinarith
    have hW0 : 0 < W := by rw [hW]; positivity
    have key : (W - a)^2 * (W + X) < ((W + X - a)^2 - (Cs - a)^2) * W := by
      have e : ((W + X - a)^2 - (X - a)^2) * W - (W - a)^2 * (W + X) =
          W*(W*X - a^2) + a*X*(2*W - a) := by ring
      have : 0 ≤ W*(W*X - a^2) := mul_nonneg (by linarith) (by nlinarith)
      have : 0 ≤ a*X*(2*W - a) := mul_nonneg (mul_nonneg hSH0 (by linarith)) (by linarith)
      have : ((W + X - a)^2 - (X - a)^2) * W < ((W + X - a)^2 - (Cs - a)^2) * W :=
        mul_lt_mul_of_pos_right (by linarith) hW0
      linarith
    have e1 : ((1 - α) * P.vH * P.Nbar - a) * ((1 - α) * P.vH * P.Nbar + a - 2 * a) =
        (W - a)^2 := by rw [hW]; ring
    have e2 : (P.vH * P.Nbar - Cs) * (P.vH * P.Nbar + Cs - 2 * a) =
        (W + X - a)^2 - (Cs - a)^2 := by rw [hV]; ring
    rw [e1, e2]
    have hNv : 2 * P.Nbar * P.vH = 2 * (W + X) := by rw [← hV]; ring
    have hNw : 2 * P.Nbar * ((1 - α) * P.vH) = 2 * W := by rw [hW]; ring
    rw [hNv, hNw]; nlinarith
  · have : Pi P.Nbar P.SH P.SH ((1 - α) * P.vH) = 0 := by unfold Pi; rw [if_neg hw]
    rw [this]; exact hVpos

end CTSol

theorem solution (P : Params) (hP : P.Standing) (α C : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hC : P.SH ≤ C) :
    |B P - 2 * (C / P.Nbar)| <
        Real.sqrt (B P ^ 2 + 4 * ((C ^ 2 - 2 * P.SL * C) / P.Nbar ^ 2)) ∧
      p1 P α C < C / (α * P.Nbar) ∧ C / (α * P.Nbar) < p2 P α C ∧
      C / P.Nbar ≤ C / (α * P.Nbar) :=
  CTSol.ms_eq8 P hP α C hα0 hα1 hC

-- Prove2me | solution 1 for BundledPay.Base.stage2_bp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:31:37.109829+00:00
-- url     : https://prove2.me/submissions/87b45091-7005-42a1-b059-ab08bd7b5956

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

lemma t1x_hosp_eq (P : Params) (hwq : P.wq = 0) (r T ih ip : ℝ) :
    hospBP P r T ih ip = r - P.c2 - P.r2p - (T + (P.dc + P.drp - T) * intensity P ih ip) := by
  simp only [hospBP, Params.dc, Params.drp, hwq]; ring

lemma t1x_phys_eq (P : Params) (T ih ip : ℝ) :
    physBP P T ih ip = P.r2p + T + (P.drp - T) * intensity P ih ip
      - P.wb * (intensity P ih ip - P.I0) ^ 2 := by
  simp only [physBP, Params.drp]; ring

lemma t1x_ffs_hosp_eq (P : Params) (hwq : P.wq = 0) (ih ip : ℝ) :
    hospFFS P ih ip = P.rh - P.c2 - P.dc * intensity P ih ip := by
  simp only [hospFFS, Params.dc, hwq]; ring

lemma t1x_ffs_phys_eq (P : Params) (ih ip : ℝ) : physFFS P ih ip = physBP P 0 ih ip := by
  simp only [physFFS, physBP]; ring

lemma t1x_rffs_eq (P : Params) (ih ip : ℝ) :
    rFFS P ih ip = P.rh + P.r2p + P.drp * intensity P ih ip := by
  simp only [rFFS, Params.drp]; ring

lemma t1x_int_one (P : Params) (ip : ℝ) : intensity P 1 ip = (1 - P.psi) * ip := by
  simp only [intensity]; ring

lemma t1x_int_zero (P : Params) (ip : ℝ) : intensity P 0 ip = P.psi + (1 - P.psi) * ip := by
  simp only [intensity]; ring

lemma t1x_int_le_one (P : Params) (hψ0 : 0 < P.psi) (hψ1 : P.psi < 1) (ih ip : ℝ)
    (hih : ih ∈ Set.Icc (0:ℝ) 1) (hip : ip ∈ Set.Icc (0:ℝ) 1) :
    intensity P ih ip ≤ 1 := by
  simp only [intensity]
  obtain ⟨a1, a2⟩ := hih
  obtain ⟨b1, b2⟩ := hip
  nlinarith [mul_nonneg (sub_nonneg.2 hψ1.le) (sub_nonneg.2 b2), mul_nonneg a1 hψ0.le]

lemma t1x_hosp_one (P : Params) (hwq : P.wq = 0) (hψ0 : 0 < P.psi) (r T ih ip : ℝ)
    (hTa : T < P.dc + P.drp) (hih : ih ≤ 1)
    (h : hospBP P r T 1 ip ≤ hospBP P r T ih ip) : ih = 1 := by
  rw [t1x_hosp_eq P hwq, t1x_hosp_eq P hwq] at h
  simp only [intensity] at h
  by_contra hne
  have hlt : ih < 1 := lt_of_le_of_ne hih hne
  have := mul_pos (mul_pos (sub_pos.2 hTa) (sub_pos.2 hlt)) hψ0
  nlinarith

lemma t1x_ffs_one (P : Params) (hwq : P.wq = 0) (hψ0 : 0 < P.psi) (hdc : 0 < P.dc)
    (ih ip : ℝ) (hih : ih ≤ 1) (h : hospFFS P 1 ip ≤ hospFFS P ih ip) : ih = 1 := by
  rw [t1x_ffs_hosp_eq P hwq, t1x_ffs_hosp_eq P hwq] at h
  simp only [intensity] at h
  by_contra hne
  have hlt : ih < 1 := lt_of_le_of_ne hih hne
  have := mul_pos (mul_pos hdc (sub_pos.2 hlt)) hψ0
  nlinarith

lemma t1x_physopt (P : Params) (hψ1 : P.psi < 1) (T ip : ℝ)
    (h : ∀ y ∈ Set.Icc (0:ℝ) 1, physBP P T 1 y ≤ physBP P T 1 ip) :
    ∀ J, 0 ≤ J → J ≤ 1 - P.psi →
      (P.drp - T) * J - P.wb * (J - P.I0) ^ 2 ≤
        (P.drp - T) * ((1 - P.psi) * ip) - P.wb * ((1 - P.psi) * ip - P.I0) ^ 2 := by
  intro J hJ0 hJ1
  have hp : 0 < 1 - P.psi := by linarith
  have hy : J / (1 - P.psi) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg hJ0 hp.le, (div_le_one hp).2 hJ1⟩
  have := h _ hy
  rw [t1x_phys_eq, t1x_phys_eq, t1x_int_one, t1x_int_one] at this
  have e : (1 - P.psi) * (J / (1 - P.psi)) = J := by field_simp
  rw [e] at this
  linarith

lemma t1x_clip (w I0 drp T v L U x : ℝ) (hw : 0 < w) (hLU : L ≤ U)
    (hv : 2 * w * v = 2 * w * I0 + drp - T) (hx0 : L ≤ x) (hx1 : x ≤ U) :
    (drp - T) * x - w * (x - I0) ^ 2 ≤
      (drp - T) * max L (min v U) - w * (max L (min v U) - I0) ^ 2 := by
  have e1 : drp - T = 2 * w * (v - I0) := by linarith
  have key : (max L (min v U) - v) ^ 2 ≤ (x - v) ^ 2 := by
    rcases le_total v L with h | h
    · rw [min_eq_left (h.trans hLU), max_eq_left h]; nlinarith
    · rcases le_total v U with h' | h'
      · rw [min_eq_left h', max_eq_right h]; nlinarith [sq_nonneg (x - v)]
      · rw [min_eq_right h', max_eq_right hLU]; nlinarith
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_left key hw.le]

lemma t1x_clipdiv (v p : ℝ) (hp : 0 < p) :
    max 0 (min 1 (v / p)) = max 0 (min v p) / p := by
  rw [eq_div_iff hp.ne', max_mul_of_nonneg _ _ hp.le, min_mul_of_nonneg _ _ hp.le, zero_mul,
    one_mul, div_mul_cancel₀ _ hp.ne', min_comm]

end BundledPay.Base

open BundledPay.Base

theorem solution (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (rBP T ih ip : ℝ) (hT : 0 ≤ T) (hTupper : T < P.dc + P.drp) :
    IsNashBP P rBP T ih ip ↔
      (ih = 1 ∧ ip = max 0 (min 1
        ((P.I0 + (P.drp - T) / (2 * P.wb)) / (1 - P.psi)))) := by
  obtain ⟨hc, hr, hw, hI0a, hI0b, hψ0, hψ1⟩ := hS
  have hp : 0 < 1 - P.psi := by linarith
  rw [t1x_clipdiv _ _ hp]
  set v := P.I0 + (P.drp - T) / (2 * P.wb) with hvdef
  have hv : 2 * P.wb * v = 2 * P.wb * P.I0 + P.drp - T := by
    rw [hvdef]; field_simp; ring
  set c := max 0 (min v (1 - P.psi)) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  have hc1 : c ≤ 1 - P.psi := max_le (by linarith) (min_le_right _ _)
  have hint : intensity P 1 (c / (1 - P.psi)) = c := by
    rw [t1x_int_one]; field_simp
  constructor
  · rintro ⟨hih, hip, hh, hph⟩
    have h1 := t1x_hosp_one P hwq hψ0 rBP T ih ip hTupper hih.2 (hh 1 ⟨zero_le_one, le_rfl⟩)
    subst h1
    refine ⟨rfl, ?_⟩
    have hopt := t1x_physopt P hψ1 T ip hph c hc0 hc1
    have e1 : P.drp - T = 2 * P.wb * (v - P.I0) := by linarith
    rw [e1] at hopt
    have hI0 : 0 ≤ (1 - P.psi) * ip := mul_nonneg hp.le hip.1
    have hI1 : (1 - P.psi) * ip ≤ 1 - P.psi := mul_le_of_le_one_right hp.le hip.2
    have hle : ((1 - P.psi) * ip - v) ^ 2 ≤ (c - v) ^ 2 := by
      have := mul_pos hw hw
      nlinarith
    have hI : (1 - P.psi) * ip = c := by
      rcases le_total v 0 with h | h
      · have hc' : c = 0 := by
          rw [hc, min_eq_left (by linarith), max_eq_left h]
        rw [hc'] at hle ⊢
        nlinarith
      · rcases le_total v (1 - P.psi) with h' | h'
        · have hc' : c = v := by rw [hc, min_eq_left h', max_eq_right h]
          rw [hc'] at hle ⊢
          nlinarith [sq_nonneg ((1 - P.psi) * ip - v)]
        · have hc' : c = 1 - P.psi := by rw [hc, min_eq_right h', max_eq_right hp.le]
          rw [hc'] at hle ⊢
          nlinarith
    rw [← hI]; field_simp
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨div_nonneg hc0 hp.le, (div_le_one hp).2 hc1⟩, ?_, ?_⟩
    · intro x hx
      rw [t1x_hosp_eq P hwq, t1x_hosp_eq P hwq]
      simp only [intensity]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hTupper.le) (sub_nonneg.2 hx.2)) hψ0.le]
    · intro y hy
      rw [t1x_phys_eq, t1x_phys_eq, hint, t1x_int_one]
      have := t1x_clip P.wb P.I0 P.drp T _ 0 (1 - P.psi) ((1 - P.psi) * y) hw hp.le hv
        (mul_nonneg hp.le hy.1) (by nlinarith [hy.2])
      rw [← hc] at this
      linarith

-- Prove2me | solution 1 for BundledPay.Base.proposition_2_eq12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:34:08.315797+00:00
-- url     : https://prove2.me/submissions/422015a6-ba50-4dd2-a6ae-16e4798848ff

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

lemma t1z_core (w ψ I0 dc drp Q T I v : ℝ) (hw : 0 < w)
    (hQ : 8 * w * Q = (dc + 2 * w * (1 - I0)) ^ 2)
    (h7 : 8 * w * (dc + drp) * ψ ≤ (dc + 2 * w * (1 - I0)) ^ 2)
    (hTa : T < dc + drp) (hIb : I ≤ 1 - ψ)
    (hv : 2 * w * v = 2 * w * I0 + drp - T)
    (hopt : ∀ J, 0 ≤ J → J ≤ 1 - ψ →
      (drp - T) * J - w * (J - I0) ^ 2 ≤ (drp - T) * I - w * (I - I0) ^ 2)
    (hψ1 : ψ < 1) (hIa : 0 ≤ I) (hT : 0 ≤ T) (hψ0 : 0 < ψ) :
    (dc + drp - Q ≤ T + (dc + drp - T) * I) ∧
    (0 ≤ v → v ≤ 1 - ψ → I = v) ∧ (1 - ψ < v → I = 1 - ψ) := by
  have e1 : drp - T = 2 * w * (v - I0) := by linarith
  have ident : 8 * w * (T + (dc + drp - T) * v - (dc + drp - Q)) =
      (2 * T - (dc + 2 * drp - 2 * w * (1 - I0))) ^ 2 := by
    linear_combination (4 * (dc + drp - T)) * hv + hQ
  have hX : 0 ≤ T + (dc + drp - T) * v - (dc + drp - Q) := by
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_pos_of_neg hw hc, sq_nonneg (2 * T - (dc + 2 * drp - 2 * w * (1 - I0)))]
  have interior : 0 ≤ v → v ≤ 1 - ψ → I = v := by
    intro h0 h1
    have := hopt v h0 h1
    rw [e1] at this
    have h2 : w * (I - v) ^ 2 ≤ 0 := by nlinarith
    have h3 : (I - v) ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hw hc]
    have h4 : (I - v) ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4
    linarith
  have top : 1 - ψ < v → I = 1 - ψ := by
    intro hv1
    have := hopt (1 - ψ) (by linarith) le_rfl
    rw [e1] at this
    by_contra hne
    have hlt : I < 1 - ψ := lt_of_le_of_ne hIb hne
    nlinarith [mul_pos hw (mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < 2 * v - I - (1 - ψ)))]
  refine ⟨?_, interior, top⟩
  rcases lt_or_ge v 0 with hv0 | hv0
  · have : 0 < (dc + drp - T) * (I - v) := mul_pos (by linarith) (by linarith)
    nlinarith
  · rcases le_or_gt v (1 - ψ) with hv1 | hv1
    · rw [interior hv0 hv1]; linarith
    · rw [top hv1]
      have hQa : (dc + drp) * ψ ≤ Q := by nlinarith
      nlinarith [mul_nonneg hT hψ0.le]

end BundledPay.Base

open BundledPay.Base

theorem solution (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi ≤ psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (ihF ipF : ℝ) (hF : IsNashFFS P ihF ipF)
    (rBP : ℝ) (σ : ℝ → ℝ × ℝ) (T : ℝ) (hBP : IsSPNE P rBP σ T) :
    savings P ihF ipF T (σ T).1 (σ T).2 =
      if P.psi ≤ psiBar P then
        (P.dc + 2 * P.drp - 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb)
      else
        (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb) -
          (P.dc + P.drp) * P.psi := by
  obtain ⟨hc, hr, hw, hI0a, hI0b, hψ0, hψ1⟩ := hS
  have hdc : 0 < P.dc := by unfold Params.dc; linarith
  have hdrp : 0 < P.drp := by unfold Params.drp; linarith
  have h6' : 4 * P.wb * P.psi ≤ 2 * P.wb * (1 - P.I0) + P.dc := by
    unfold psiPlus at h6; rw [le_div_iff₀ (by positivity)] at h6; linarith
  have h7' : 8 * P.wb * (P.dc + P.drp) * P.psi ≤ (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 := by
    unfold psi0 at h7; rw [le_div_iff₀ (by positivity)] at h7; linarith
  have hp : 0 < 1 - P.psi := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, 8 * P.wb * Q = (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 :=
    ⟨(P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb), by field_simp⟩
  have hQpos : 0 < Q := by
    have : 0 < (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 := by
      have : 0 < P.dc + 2 * P.wb * (1 - P.I0) := by nlinarith
      positivity
    nlinarith
  have upper : ∀ r T ih ip, 0 ≤ T → IsNashBP P r T ih ip →
      hospBP P r T ih ip ≤ r - P.c2 - P.r2p - (P.dc + P.drp - Q) := by
    intro r T ih ip hT hN
    obtain ⟨hih, hip, hh, hph⟩ := hN
    by_cases hTa : T < P.dc + P.drp
    · have h1 := t1x_hosp_one P hwq hψ0 r T ih ip hTa hih.2 (hh 1 ⟨zero_le_one, le_rfl⟩)
      subst h1
      rw [t1x_hosp_eq P hwq, t1x_int_one]
      have hopt := t1x_physopt P hψ1 T ip hph
      obtain ⟨v, hv⟩ : ∃ v : ℝ, 2 * P.wb * v = 2 * P.wb * P.I0 + P.drp - T :=
        ⟨(2 * P.wb * P.I0 + P.drp - T) / (2 * P.wb), by field_simp⟩
      have core := t1z_core P.wb P.psi P.I0 P.dc P.drp Q T ((1 - P.psi) * ip) v hw
        hQ h7' hTa (mul_le_of_le_one_right hp.le hip.2) hv hopt hψ1 (mul_nonneg hp.le hip.1) hT hψ0
      linarith [core.1]
    · push Not at hTa
      have hI1 := t1x_int_le_one P hψ0 hψ1 ih ip hih hip
      rw [t1x_hosp_eq P hwq]
      have := mul_nonneg (sub_nonneg.2 hTa) (sub_nonneg.2 hI1)
      nlinarith
  set TS : ℝ := (P.dc + 2 * P.drp - 2 * P.wb * (1 - P.I0)) / 2 with hTS
  have hTS0 : 0 < TS := by rw [hTS]; linarith
  have hTSa : TS < P.dc + P.drp := by rw [hTS]; nlinarith
  have attained : ∀ r ih ip, IsNashBP P r TS ih ip →
      hospBP P r TS ih ip = r - P.c2 - P.r2p - (P.dc + P.drp - Q) := by
    intro r ih ip hN
    obtain ⟨hih, hip, hh, hph⟩ := hN
    have h1 := t1x_hosp_one P hwq hψ0 r TS ih ip hTSa hih.2 (hh 1 ⟨zero_le_one, le_rfl⟩)
    subst h1
    rw [t1x_hosp_eq P hwq, t1x_int_one]
    have hopt := t1x_physopt P hψ1 TS ip hph
    set vS : ℝ := (2 * (1 + P.I0) * P.wb - P.dc) / (4 * P.wb) with hvS
    have hv : 2 * P.wb * vS = 2 * P.wb * P.I0 + P.drp - TS := by
      rw [hvS, hTS]; field_simp; ring
    have core := t1z_core P.wb P.psi P.I0 P.dc P.drp Q TS ((1 - P.psi) * ip) vS hw
      hQ h7' hTSa (mul_le_of_le_one_right hp.le hip.2) hv hopt hψ1 (mul_nonneg hp.le hip.1) hTS0.le hψ0
    have hv0 : 0 ≤ vS := by rw [hvS]; apply div_nonneg <;> nlinarith
    have hv1 : vS ≤ 1 - P.psi := by
      rw [hvS, div_le_iff₀ (by positivity)]; nlinarith
    rw [core.2.1 hv0 hv1]
    have : TS + (P.dc + P.drp - TS) * vS = P.dc + P.drp - Q := by
      have e8 : 8 * P.wb * (TS + (P.dc + P.drp - TS) * vS) = 8 * P.wb * (P.dc + P.drp - Q) := by
        rw [hvS, hTS]; field_simp; linear_combination hQ
      exact mul_left_cancel₀ (by positivity : (8 * P.wb) ≠ 0) e8
    linarith
  -- the SPNE value
  obtain ⟨hT, hN, hmax⟩ := hBP
  have hT' : (0:ℝ) ≤ T := hT
  have hge := hmax TS (le_of_lt hTS0)
  rw [attained _ _ _ (hN TS (le_of_lt hTS0))] at hge
  have hu := upper _ T _ _ hT' (hN T hT)
  rw [t1x_hosp_eq P hwq] at hge hu
  have hφ : T + (P.dc + P.drp - T) * intensity P (σ T).1 (σ T).2 = P.dc + P.drp - Q := by
    linarith
  -- FFS
  obtain ⟨hihF, hipF, hhF, hpF⟩ := hF
  have h1F := t1x_ffs_one P hwq hψ0 hdc ihF ipF hihF.2 (hhF 1 ⟨zero_le_one, le_rfl⟩)
  subst h1F
  have hoptF := t1x_physopt P hψ1 0 ipF (fun y hy => by
    rw [← t1x_ffs_phys_eq, ← t1x_ffs_phys_eq]; exact hpF y hy)
  set v0 : ℝ := P.I0 + P.drp / (2 * P.wb) with hv0def
  have hv0 : 2 * P.wb * v0 = 2 * P.wb * P.I0 + P.drp - 0 := by
    rw [hv0def]; field_simp; ring
  have coreF := t1z_core P.wb P.psi P.I0 P.dc P.drp Q 0 ((1 - P.psi) * ipF) v0 hw
    hQ h7' (by linarith) (mul_le_of_le_one_right hp.le hipF.2) hv0 hoptF hψ1
    (mul_nonneg hp.le hipF.1) le_rfl hψ0
  have hsav : savings P 1 ipF T (σ T).1 (σ T).2 =
      (P.dc + P.drp) * ((1 - P.psi) * ipF) - (P.dc + P.drp - Q) := by
    unfold savings breakEvenBP
    rw [t1x_rffs_eq, t1x_ffs_hosp_eq P hwq, t1x_hosp_eq P hwq, t1x_int_one]
    linarith
  rw [hsav]
  have hv0pos : 0 ≤ v0 := by rw [hv0def]; positivity
  split_ifs with hψ
  · have hv1 : v0 ≤ 1 - P.psi := by
      unfold psiBar at hψ; rw [hv0def]; linarith
    rw [coreF.2.1 hv0pos hv1, eq_div_iff (by positivity)]
    linear_combination (4 * (P.dc + P.drp)) * hv0 + hQ
  · have hv1 : 1 - P.psi < v0 := by
      unfold psiBar at hψ; rw [hv0def]; linarith
    rw [coreF.2.2 hv1]
    have hQ' : Q = (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [← hQ']
    ring

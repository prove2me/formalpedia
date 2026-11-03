-- Prove2me | solution 1 for BundledPay.Base.physician_gain
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:31:36.064899+00:00
-- url     : https://prove2.me/submissions/16c86d2b-f778-4c14-9400-fd2b084d6ea5

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

lemma t1x_core (w ψ I0 dc drp Q T I v : ℝ) (hw : 0 < w) (hψ0 : 0 < ψ) (hψ1 : ψ < 1)
    (hdc : 0 < dc) (hdrp : 0 < drp) (hI0 : 0 ≤ I0) (hI0' : I0 ≤ 1)
    (hQ : 8 * w * Q = (dc + 2 * w * (1 - I0)) ^ 2)
    (h5 : 2 * w * (1 - I0) < dc + 2 * drp)
    (h7 : 8 * w * (dc + drp) * ψ < (dc + 2 * w * (1 - I0)) ^ 2)
    (hT : 0 ≤ T) (hTa : T < dc + drp) (hIa : 0 ≤ I) (hIb : I ≤ 1 - ψ)
    (hv : 2 * w * v = 2 * w * I0 + drp - T)
    (hopt : ∀ J, 0 ≤ J → J ≤ 1 - ψ →
      (drp - T) * J - w * (J - I0) ^ 2 ≤ (drp - T) * I - w * (I - I0) ^ 2) :
    (dc + drp - Q ≤ T + (dc + drp - T) * I) ∧
    (T = 0 → dc + drp - Q < T + (dc + drp - T) * I) ∧
    (0 ≤ v → v ≤ 1 - ψ → I = v) := by
  have e1 : drp - T = 2 * w * (v - I0) := by linarith
  have ident : 8 * w * (T + (dc + drp - T) * v - (dc + drp - Q)) =
      (2 * T - (dc + 2 * drp - 2 * w * (1 - I0))) ^ 2 := by
    linear_combination (4 * (dc + drp - T)) * hv + hQ
  have hE : 0 < dc + 2 * drp - 2 * w * (1 - I0) := by linarith
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
  refine ⟨?_, ?_, interior⟩
  · rcases lt_or_ge v 0 with hv0 | hv0
    · have : 0 < (dc + drp - T) * (I - v) := mul_pos (by linarith) (by linarith)
      nlinarith
    · rcases le_or_gt v (1 - ψ) with hv1 | hv1
      · rw [interior hv0 hv1]; linarith
      · rw [top hv1]
        have hQa : (dc + drp) * ψ < Q := by nlinarith
        nlinarith
  · intro hT0
    rcases lt_or_ge v 0 with hv0 | hv0
    · have : 0 < (dc + drp - T) * (I - v) := mul_pos (by linarith) (by linarith)
      nlinarith
    · rcases le_or_gt v (1 - ψ) with hv1 | hv1
      · rw [interior hv0 hv1]
        have hpos : 0 < T + (dc + drp - T) * v - (dc + drp - Q) := by
          have hsq : 0 < (2 * T - (dc + 2 * drp - 2 * w * (1 - I0))) ^ 2 := by
            have : 2 * T - (dc + 2 * drp - 2 * w * (1 - I0)) ≠ 0 := by rw [hT0]; linarith
            positivity
          rw [← ident] at hsq
          exact (mul_pos_iff_of_pos_left (by positivity)).1 hsq
        linarith
      · rw [top hv1]
        have hQa : (dc + drp) * ψ < Q := by nlinarith
        nlinarith

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

noncomputable def t1x_sigma (P : Params) (T : ℝ) : ℝ × ℝ :=
  if T < P.dc + P.drp then
    (1, max 0 (min (P.I0 + (P.drp - T) / (2 * P.wb)) (1 - P.psi)) / (1 - P.psi))
  else
    (0, (max P.psi (min (P.I0 + (P.drp - T) / (2 * P.wb)) 1) - P.psi) / (1 - P.psi))

lemma t1x_sigma_nash (P : Params) (hwq : P.wq = 0) (hw : 0 < P.wb) (hψ0 : 0 < P.psi)
    (hψ1 : P.psi < 1) (r T : ℝ) :
    IsNashBP P r T (t1x_sigma P T).1 (t1x_sigma P T).2 := by
  have hp : 0 < 1 - P.psi := by linarith
  have hv : 2 * P.wb * (P.I0 + (P.drp - T) / (2 * P.wb)) = 2 * P.wb * P.I0 + P.drp - T := by
    field_simp; ring
  unfold t1x_sigma
  split_ifs with hTa
  · set c := max 0 (min (P.I0 + (P.drp - T) / (2 * P.wb)) (1 - P.psi)) with hc
    have hc0 : 0 ≤ c := le_max_left _ _
    have hc1 : c ≤ 1 - P.psi := max_le (by linarith) (min_le_right _ _)
    have hint : intensity P 1 (c / (1 - P.psi)) = c := by
      rw [t1x_int_one]; field_simp
    refine ⟨⟨zero_le_one, le_rfl⟩, ⟨div_nonneg hc0 hp.le, (div_le_one hp).2 hc1⟩, ?_, ?_⟩
    · intro x hx
      rw [t1x_hosp_eq P hwq, t1x_hosp_eq P hwq]
      simp only [intensity]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hTa.le) (sub_nonneg.2 hx.2)) hψ0.le]
    · intro y hy
      rw [t1x_phys_eq, t1x_phys_eq, hint, t1x_int_one]
      have := t1x_clip P.wb P.I0 P.drp T _ 0 (1 - P.psi) ((1 - P.psi) * y) hw hp.le hv
        (mul_nonneg hp.le hy.1) (by nlinarith [hy.2])
      rw [← hc] at this
      linarith
  · push Not at hTa
    set c := max P.psi (min (P.I0 + (P.drp - T) / (2 * P.wb)) 1) with hc
    have hc0 : P.psi ≤ c := le_max_left _ _
    have hc1 : c ≤ 1 := max_le hψ1.le (min_le_right _ _)
    have hint : intensity P 0 ((c - P.psi) / (1 - P.psi)) = c := by
      rw [t1x_int_zero]; field_simp; ring
    refine ⟨⟨le_rfl, zero_le_one⟩,
      ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).2 (by linarith)⟩, ?_, ?_⟩
    · intro x hx
      rw [t1x_hosp_eq P hwq, t1x_hosp_eq P hwq]
      simp only [intensity]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hTa) hx.1) hψ0.le]
    · intro y hy
      rw [t1x_phys_eq, t1x_phys_eq, hint, t1x_int_zero]
      have := t1x_clip P.wb P.I0 P.drp T _ P.psi 1 (P.psi + (1 - P.psi) * y) hw hψ1.le hv
        (by nlinarith [mul_nonneg hp.le hy.1]) (by nlinarith [hy.2])
      rw [← hc] at this
      linarith

end BundledPay.Base

open BundledPay.Base

theorem solution (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (h5 : 2 * P.wb * (1 - P.I0) < P.dc + 2 * P.drp)
    (h6 : P.psi ≤ psiPlus P)
    (h7 : P.psi < psi0 P)
    (hint : P.dc < 2 * P.wb * (1 + P.I0))
    (ihF ipF : ℝ) (hF : IsNashFFS P ihF ipF)
    (rBP : ℝ) (σ : ℝ → ℝ × ℝ) (T : ℝ) (hBP : IsSPNE P rBP σ T) :
    physFFS P ihF ipF < physBP P T (σ T).1 (σ T).2 := by
  obtain ⟨hc, hr, hw, hI0a, hI0b, hψ0, hψ1⟩ := hS
  have hdc : 0 < P.dc := by unfold Params.dc; linarith
  have hdrp : 0 < P.drp := by unfold Params.drp; linarith
  have h6' : 4 * P.wb * P.psi ≤ 2 * P.wb * (1 - P.I0) + P.dc := by
    unfold psiPlus at h6; rw [le_div_iff₀ (by positivity)] at h6; linarith
  have h7' : 8 * P.wb * (P.dc + P.drp) * P.psi < (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 := by
    unfold psi0 at h7; rw [lt_div_iff₀ (by positivity)] at h7; linarith
  have hp : 0 < 1 - P.psi := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, 8 * P.wb * Q = (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 :=
    ⟨(P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 / (8 * P.wb), by field_simp⟩
  have hQpos : 0 < Q := by
    have : 0 < (P.dc + 2 * P.wb * (1 - P.I0)) ^ 2 := by
      have : 0 < P.dc + 2 * P.wb * (1 - P.I0) := by nlinarith
      positivity
    nlinarith
  -- upper bound on the hospital's stage-2 payoff
  have upper : ∀ r T ih ip, 0 ≤ T → IsNashBP P r T ih ip →
      hospBP P r T ih ip ≤ r - P.c2 - P.r2p - (P.dc + P.drp - Q) ∧
      ((T = 0 ∨ P.dc + P.drp ≤ T) →
        hospBP P r T ih ip < r - P.c2 - P.r2p - (P.dc + P.drp - Q)) := by
    intro r T ih ip hT hN
    obtain ⟨hih, hip, hh, hph⟩ := hN
    by_cases hTa : T < P.dc + P.drp
    · have h1 := t1x_hosp_one P hwq hψ0 r T ih ip hTa hih.2 (hh 1 ⟨zero_le_one, le_rfl⟩)
      subst h1
      rw [t1x_hosp_eq P hwq, t1x_int_one]
      have hopt := t1x_physopt P hψ1 T ip hph
      obtain ⟨v, hv⟩ : ∃ v : ℝ, 2 * P.wb * v = 2 * P.wb * P.I0 + P.drp - T :=
        ⟨(2 * P.wb * P.I0 + P.drp - T) / (2 * P.wb), by field_simp⟩
      have core := t1x_core P.wb P.psi P.I0 P.dc P.drp Q T ((1 - P.psi) * ip) v hw hψ0 hψ1
        hdc hdrp hI0a hI0b hQ h5 h7' hT hTa (mul_nonneg hp.le hip.1)
        (by nlinarith [hip.2]) hv hopt
      refine ⟨by linarith [core.1], ?_⟩
      rintro (h0 | h0)
      · linarith [core.2.1 h0]
      · exact absurd h0 (not_le.2 hTa)
    · push Not at hTa
      have hI1 := t1x_int_le_one P hψ0 hψ1 ih ip hih hip
      rw [t1x_hosp_eq P hwq]
      have := mul_nonneg (sub_nonneg.2 hTa) (sub_nonneg.2 hI1)
      constructor
      · nlinarith
      · intro _; nlinarith
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
    have core := t1x_core P.wb P.psi P.I0 P.dc P.drp Q TS ((1 - P.psi) * ip) vS hw hψ0 hψ1
      hdc hdrp hI0a hI0b hQ h5 h7' hTS0.le hTSa (mul_nonneg hp.le hip.1)
      (by nlinarith [hip.2]) hv hopt
    have hv0 : 0 ≤ vS := by rw [hvS]; apply div_nonneg <;> nlinarith
    have hv1 : vS ≤ 1 - P.psi := by
      rw [hvS, div_le_iff₀ (by positivity)]; nlinarith
    rw [core.2.2 hv0 hv1]
    have : TS + (P.dc + P.drp - TS) * vS = P.dc + P.drp - Q := by
      have e8 : 8 * P.wb * (TS + (P.dc + P.drp - TS) * vS) = 8 * P.wb * (P.dc + P.drp - Q) := by
        rw [hvS, hTS]; field_simp; linear_combination hQ
      have := mul_left_cancel₀ (by positivity : (8 * P.wb) ≠ 0) e8
      exact this
    linarith
  obtain ⟨hihF, hipF, hhF, hpF⟩ := hF
  have h1F := t1x_ffs_one P hwq hψ0 hdc ihF ipF hihF.2 (hhF 1 ⟨zero_le_one, le_rfl⟩)
  subst h1F
  obtain ⟨hT, hN, hmax⟩ := hBP
  have hT' : (0:ℝ) ≤ T := hT
  have hge := hmax TS (le_of_lt hTS0)
  rw [attained _ _ _ (hN TS (le_of_lt hTS0))] at hge
  have hu := upper _ T _ _ hT' (hN T hT)
  have hT0 : 0 < T := by
    rcases hT'.eq_or_lt with h | h
    · have := hu.2 (Or.inl h.symm); linarith
    · exact h
  have hTa : T < P.dc + P.drp := by
    by_contra hc
    push Not at hc
    have := hu.2 (Or.inr hc); linarith
  obtain ⟨hih, hip, hh, hph⟩ := hN T hT
  have h1 := t1x_hosp_one P hwq hψ0 _ T _ _ hTa hih.2 (hh 1 ⟨zero_le_one, le_rfl⟩)
  rw [h1]
  have := hph ipF hipF
  rw [h1] at this
  rw [t1x_ffs_phys_eq]
  rw [t1x_phys_eq, t1x_phys_eq, t1x_int_one, t1x_int_one] at this ⊢
  have hIF1 : (1 - P.psi) * ipF ≤ 1 - P.psi := mul_le_of_le_one_right hp.le hipF.2
  have : 0 < T * (1 - (1 - P.psi) * ipF) := mul_pos hT0 (by linarith)
  linarith

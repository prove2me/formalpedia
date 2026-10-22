-- Prove2me | solution 1 for CurbEmissions.ExactStandard.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:51:36.597671+00:00
-- url     : https://prove2.me/submissions/721d1d4e-34a9-4d42-9f0b-3bd14d7b8081

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

set_option autoImplicit false

namespace CE3Aux
open CurbEmissions.ExactStandard

/-- Per-unit-market regulator welfare at a common standard `s`. -/
noncomputable def phi (P : Params) (s : ℝ) : ℝ :=
  margin P s ^ 2 / (8 * P.ubar) - P.h1 * (P.b - s) * margin P s / (2 * P.ubar)

/-- Unclipped version of `phi`. -/
noncomputable def phiRaw (P : Params) (s : ℝ) : ℝ :=
  (P.ubar - (P.c - P.gam) * s) ^ 2 / (8 * P.ubar)
    - P.h1 * (P.b - s) * (P.ubar - (P.c - P.gam) * s) / (2 * P.ubar)

lemma margin_of {P : Params} {e : ℝ} (h : 0 ≤ P.ubar - (P.c - P.gam) * e) :
    margin P e = P.ubar - (P.c - P.gam) * e := max_eq_right h

lemma margin_of_nonpos {P : Params} {e : ℝ} (h : P.ubar - (P.c - P.gam) * e ≤ 0) :
    margin P e = 0 := max_eq_left h

lemma margin_zero {P : Params} (hu : 0 < P.ubar) : margin P 0 = P.ubar := by
  unfold margin; rw [mul_zero, sub_zero]; exact max_eq_right hu.le

lemma phi_of {P : Params} {s : ℝ} (h : 0 ≤ P.ubar - (P.c - P.gam) * s) :
    phi P s = phiRaw P s := by
  unfold phi phiRaw; rw [margin_of h]

lemma phi_of_nonpos {P : Params} {s : ℝ} (h : P.ubar - (P.c - P.gam) * s ≤ 0) :
    phi P s = 0 := by
  unfold phi; rw [margin_of_nonpos h]; ring

lemma saStar_eq (P : Params) (hk : 0 < P.c - P.gam) (hA : 0 < 4 * P.h1 - (P.c - P.gam)) :
    (P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)) * saStar P
      = 2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar := by
  unfold saStar; rw [mul_comm]; exact div_mul_cancel₀ _ (mul_ne_zero hk.ne' hA.ne')

lemma phiRaw_diff (P : Params) (hk : 0 < P.c - P.gam) (hA : 0 < 4 * P.h1 - (P.c - P.gam))
    (s : ℝ) :
    phiRaw P (saStar P) - phiRaw P s
      = (4 * P.h1 - (P.c - P.gam)) * (P.c - P.gam) * (s - saStar P) ^ 2 / (8 * P.ubar) := by
  have hseq := saStar_eq P hk hA
  unfold phiRaw
  linear_combination (-(saStar P - s) / (4 * P.ubar)) * hseq

lemma hW_aux (X y u h d k : ℝ) (hu : u ≠ 0) (hh : h ≠ 0) (hd : d ≠ 0) (h4 : 4 - k / h = d / h)
    (hX : d * y = 2 * h * X) : X ^ 2 / (u * (4 - k / h) ^ 2) = y ^ 2 / (4 * u) := by
  rw [h4]
  have : X = d * y / (2 * h) := by field_simp; linarith
  rw [this]; field_simp; try ring

lemma mdc (k u : ℝ) (hk : k ≠ 0) : k * (u / k) = u := by field_simp

lemma sub_div_aux (u k s : ℝ) (hk : k ≠ 0) : u / k - s = (u - k * s) / k := by field_simp

lemma back_aux (u k s : ℝ) (hk : k ≠ 0) : (u - (u - k * s)) / k = s := by
  rw [sub_sub_cancel, mul_div_cancel_left₀ _ hk]

lemma hF_aux (m1 m2 u h b k x : ℝ) (hu : u ≠ 0) (hk : k ≠ 0) :
    m1 / (8 * u) * (u - k * ((u - x) / k)) ^ 2
      - h * (b - (u - x) / k) * (m1 + m2) / (2 * u) * (u - k * ((u - x) / k))
    = (m1 / (8 * u) - h * (m1 + m2) / (2 * u * k)) * x ^ 2
      + h * (m1 + m2) * (u - b * k) / (2 * u * k) * x := by
  field_simp; try ring

lemma Th_eq (P : Params) (s : ℝ) : Th P s = (P.m1 + P.m2) * phi P s := by
  simp only [Th, pi1, pi2, consUtil, sales, phi]; ring

lemma pi1D_eq (P : Params) (s : ℝ) :
    pi1 P s .D = P.m1 * phi P s - P.h1 * P.b * sales P 0 P.m2 := by
  simp only [pi1, phi, consUtil, sales]; ring

lemma pi12D_eq (P : Params) (s : ℝ) :
    pi1 P s .D + pi2 P s .D = P.m1 * phi P s + P.m2 * phi P 0 := by
  simp only [pi1, pi2, phi, consUtil, sales]; ring

lemma pi1U_eq (P : Params) (s : ℝ) (h : 0 ≤ P.ubar - (P.c - P.gam) * s) :
    pi1 P s .U = pi1URaw P s := by
  simp only [pi1, consUtil, sales]; rw [margin_of h]; unfold pi1URaw; ring

lemma pi1D_raw (P : Params) (hu : 0 < P.ubar) (s : ℝ) (h : 0 ≤ P.ubar - (P.c - P.gam) * s) :
    pi1 P s .D = pi1DRaw P s := by
  have hu' := hu.ne'
  simp only [pi1, consUtil, sales]; rw [margin_of h, margin_zero hu]; unfold pi1DRaw
  field_simp; try ring

lemma share_arg (P : Params) (hu : 0 < P.ubar) (e : ℝ) :
    1 - (pStar P e - P.gam * e) / P.ubar = (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) := by
  have hu' := hu.ne'
  unfold pStar; field_simp; try ring

lemma prof_eq (P : Params) (hu : 0 < P.ubar) (e m : ℝ) (h0 : 0 ≤ P.ubar - (P.c - P.gam) * e)
    (h1 : P.ubar - (P.c - P.gam) * e ≤ 2 * P.ubar) :
    priceObj P e m (pStar P e) = m * ((P.ubar - (P.c - P.gam) * e) ^ 2 / (4 * P.ubar)) := by
  have hu' := hu.ne'
  have hle : (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact h1
  have hge : 0 ≤ (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) := div_nonneg h0 (by linarith)
  unfold priceObj share
  rw [share_arg P hu e, max_eq_right hge, min_eq_right hle]
  unfold pStar; field_simp; try ring

lemma prof_zero (P : Params) (hu : 0 < P.ubar) (e m : ℝ) (h0 : P.ubar - (P.c - P.gam) * e ≤ 0) :
    priceObj P e m (pStar P e) = 0 := by
  have hle : (P.ubar - (P.c - P.gam) * e) / (2 * P.ubar) ≤ 0 :=
    div_nonpos_iff.2 (Or.inr ⟨h0, by linarith⟩)
  unfold priceObj share
  rw [share_arg P hu e, max_eq_left hle, min_eq_right zero_le_one, mul_zero]

lemma prof0 (P : Params) (hu : 0 < P.ubar) (m : ℝ) :
    priceObj P 0 m (pStar P 0) = m * (P.ubar / 4) := by
  have hu' := hu.ne'
  rw [prof_eq P hu 0 m (by rw [mul_zero, sub_zero]; exact hu.le)
    (by rw [mul_zero, sub_zero]; linarith)]
  rw [mul_zero, sub_zero]; congr 1
  rw [div_eq_div_iff (mul_ne_zero four_ne_zero hu') four_ne_zero]; ring

/-- A concave quadratic is below its value at the largest solution of `= C` beyond it. -/
lemma quad_le (a β C xbar : ℝ) (ha : a < 0) (hC : a * xbar ^ 2 + β * xbar = C)
    (hg : ∀ z, a * z ^ 2 + β * z = C → z ≤ xbar) (x : ℝ) (hx : xbar ≤ x) :
    a * x ^ 2 + β * x ≤ C := by
  have hz : a * (-β / a) + β = 0 := by
    rw [mul_comm, div_mul_cancel₀ _ ha.ne]; ring
  have h2 : a * (-β / a - xbar) ^ 2 + β * (-β / a - xbar) = C := by
    linear_combination hC + (-β / a - xbar - xbar) * hz
  have hx2 := hg _ h2
  have key : a * x ^ 2 + β * x - C = a * ((x - xbar) * (x - (-β / a - xbar))) := by
    linear_combination hC + (x - xbar) * hz
  have hp : 0 ≤ (x - xbar) * (x - (-β / a - xbar)) :=
    mul_nonneg (sub_nonneg.2 hx) (by linarith)
  nlinarith

set_option maxHeartbeats 1600000 in
theorem main (P : Params) (hP : Standing P) (xbar : ℝ)
    (hx : IsGreatest (xbarEqSet P) xbar) (hc : Cond1 P xbar) :
    (∃ s1, IsBaseEq P s1 .D) ∧
    ∀ s1, IsBaseEq P s1 .D →
      let D1 := pi1 P s1 .D
      let D2 := pi2 P s1 .D
      let se := (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
                  ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)))
      (NBS P D1 D2).Nonempty ∧
      (∀ q ∈ NBS P D1 D2, q.1 = se) ∧
      D1 + D2 < Th P se ∧
      emissions P se .U < emissions P s1 .D := by
  obtain ⟨hc0, hgc, hr, hm1, hm2, hb, hh1, hu1, hu2⟩ := hP
  obtain ⟨-, hrle⟩ := hc
  simp only [le_min_iff] at hrle
  obtain ⟨⟨hT1, hT2⟩, hT3⟩ := hrle
  have hk : 0 < P.c - P.gam := by linarith
  have hh : 0 < P.h1 := by linarith
  have hA : 0 < 4 * P.h1 - (P.c - P.gam) := by linarith
  have hk' := hk.ne'
  have hh' := hh.ne'
  have hA' := hA.ne'
  have hu4 : 4 * P.r < P.ubar * P.m2 := by
    rw [div_le_iff₀ (mul_pos hm1 hm2)] at hu1
    have h1' : P.m1 * (4 * P.r) < P.m1 * (P.ubar * P.m2) := by linarith [mul_pos hr hm2]
    exact lt_of_mul_lt_mul_left h1' hm1.le
  have hu : 0 < P.ubar := by
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_right h hm2.le]
  have hu' := hu.ne'
  have hm0 := margin_zero (P := P) hu
  -- the common optimum y = u - k se
  have hseq := saStar_eq P hk hA
  have hyd : (4 * P.h1 - (P.c - P.gam)) * (P.ubar - (P.c - P.gam) * saStar P)
      = 2 * P.h1 * (P.ubar - P.b * (P.c - P.gam)) := by
    linear_combination (-1 : ℝ) * hseq
  have hy0 : 0 ≤ P.ubar - (P.c - P.gam) * saStar P := by
    by_contra h; push_neg at h
    linarith [mul_pos hA (neg_pos.2 h), mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hh.le) (sub_nonneg.2 hu2)]
  have h4 : 4 - (P.c - P.gam) / P.h1 = (4 * P.h1 - (P.c - P.gam)) / P.h1 := by
    rw [sub_div (4 * P.h1) (P.c - P.gam) P.h1, mul_div_assoc, div_self hh', mul_one]
  have hW : (P.ubar - P.b * (P.c - P.gam)) ^ 2 / (P.ubar * (4 - (P.c - P.gam) / P.h1) ^ 2)
      = (P.ubar - (P.c - P.gam) * saStar P) ^ 2 / (4 * P.ubar) :=
    hW_aux _ _ _ _ _ _ hu' hh' hA' h4 hyd
  obtain ⟨W, hWd⟩ : ∃ W, (P.ubar - (P.c - P.gam) * saStar P) ^ 2 / (4 * P.ubar) = W := ⟨_, rfl⟩
  have hT1' : P.r ≤ P.m2 * (P.ubar / 4) - P.m2 * W := by
    have e : P.m2 * (P.ubar - P.b * (P.c - P.gam)) ^ 2 /
        (P.ubar * (4 - (P.c - P.gam) / P.h1) ^ 2) = P.m2 * W := by
      rw [← hWd, ← hW]; ring
    have e2 : P.m2 * P.ubar / 4 = P.m2 * (P.ubar / 4) := by ring
    linarith
  have hT2' : P.r ≤ P.m1 * W := by
    have e : P.m1 * (P.ubar - P.b * (P.c - P.gam)) ^ 2 /
        (P.ubar * (4 - (P.c - P.gam) / P.h1) ^ 2) = P.m1 * W := by
      rw [← hWd, ← hW]; ring
    linarith
  have hWu : W < P.ubar / 4 := by
    have : P.m2 * W < P.m2 * (P.ubar / 4) := by linarith
    exact lt_of_mul_lt_mul_left this hm2.le
  have hWpos : 0 < W := by
    have : 0 < P.m1 * W := by linarith
    exact pos_of_mul_pos_right this hm1.le
  have hyu : P.ubar - (P.c - P.gam) * saStar P < P.ubar := by
    rw [← hWd, div_lt_iff₀ (by linarith)] at hWu
    by_contra h; push_neg at h
    nlinarith [mul_self_le_mul_self hu.le h]
  have hypos : 0 < P.ubar - (P.c - P.gam) * saStar P := by
    rcases hy0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hWd; rw [← hWd] at hWpos; simp at hWpos
  have hse : 0 < saStar P := by
    have : 0 < (P.c - P.gam) * saStar P := by linarith
    by_contra h; push_neg at h; linarith [mul_le_mul_of_nonneg_left h hk.le]
  -- phi has a unique maximum at saStar
  have hphiS : phi P (saStar P) = phiRaw P (saStar P) := phi_of hy0
  have hpos : 0 < phiRaw P (saStar P) := by
    have hku : (P.c - P.gam) * (P.ubar / (P.c - P.gam)) = P.ubar := mdc _ _ hk'
    have h0 : phiRaw P (P.ubar / (P.c - P.gam)) = 0 := by
      unfold phiRaw; rw [hku]; ring
    have hd := phiRaw_diff P hk hA (P.ubar / (P.c - P.gam))
    rw [h0, sub_zero] at hd
    have he : P.ubar / (P.c - P.gam) - saStar P
        = (P.ubar - (P.c - P.gam) * saStar P) / (P.c - P.gam) := sub_div_aux _ _ _ hk'
    rw [hd, he]
    apply div_pos _ (by linarith)
    exact mul_pos (mul_pos hA hk) (pow_pos (div_pos hypos hk) 2)
  have hphi_lt : ∀ s, s ≠ saStar P → phi P s < phi P (saStar P) := by
    intro s hs
    rw [hphiS]
    rcases le_or_gt 0 (P.ubar - (P.c - P.gam) * s) with h | h
    · rw [phi_of h]
      have hd := phiRaw_diff P hk hA s
      have hsq : 0 < (s - saStar P) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hs)))
      have : 0 < (4 * P.h1 - (P.c - P.gam)) * (P.c - P.gam) * (s - saStar P) ^ 2
          / (8 * P.ubar) := div_pos (mul_pos (mul_pos hA hk) hsq) (by linarith)
      linarith
    · rw [phi_of_nonpos h.le]; exact hpos
  have hphi_le : ∀ s, phi P s ≤ phi P (saStar P) := by
    intro s
    by_cases h : s = saStar P
    · rw [h]
    · exact (hphi_lt s h).le
  -- firm best response at saStar is D
  have hprofS : ∀ m, priceObj P (saStar P) m (pStar P (saStar P)) = m * W := by
    intro m; rw [prof_eq P hu _ m hy0 (by linarith), hWd]
  have hDBR : IsFirmBR P (saStar P) .D := by
    intro σ'
    cases σ'
    · exact le_refl _
    · simp only [firmProfit]; rw [hprofS, hprofS, prof0 P hu]; linarith
    · simp only [firmProfit]; rw [hprofS, prof0 P hu]; linarith
  have hs1D : s1DStar P = saStar P := by unfold s1DStar saStar; ring
  -- the quadratic in x
  obtain ⟨a, had⟩ : ∃ a, P.m1 / (8 * P.ubar) - P.h1 * (P.m1 + P.m2) / (2 * P.ubar * (P.c - P.gam))
      = a := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β, P.h1 * (P.m1 + P.m2) * (P.ubar - P.b * (P.c - P.gam))
      / (2 * P.ubar * (P.c - P.gam)) = β := ⟨_, rfl⟩
  have hF : ∀ x, pi1URaw P ((P.ubar - x) / (P.c - P.gam)) = a * x ^ 2 + β * x := by
    intro x; rw [← had, ← hβd]; unfold pi1URaw; exact hF_aux _ _ _ _ _ _ x hu' hk'
  have ha : a < 0 := by
    rw [← had, sub_neg, div_lt_div_iff₀ (by linarith) (mul_pos (mul_pos (by norm_num) hu) hk)]
    linarith [mul_nonneg (mul_nonneg hu.le (sub_nonneg.2 hh1)) (add_pos hm1 hm2).le,
      mul_pos (mul_pos hu hk) hm1, mul_pos (mul_pos hu hk) hm2]
  have hC : a * xbar ^ 2 + β * xbar = pi1DRaw P (s1DStar P) := by
    rw [← hF]; exact hx.1
  have hg : ∀ z, a * z ^ 2 + β * z = pi1DRaw P (s1DStar P) → z ≤ xbar := by
    intro z hz; apply hx.2
    show pi1URaw P ((P.ubar - z) / (P.c - P.gam)) = pi1DRaw P (s1DStar P)
    rw [hF]; exact hz
  have hpiD : pi1 P (saStar P) .D = pi1DRaw P (s1DStar P) := by
    rw [hs1D]; exact pi1D_raw P hu _ hy0
  -- the base-model outcome
  have hbase : IsBaseEq P (saStar P) .D := by
    refine ⟨hse.le, hDBR, ?_⟩
    intro s' σ' hs' hBR
    cases σ'
    · rw [pi1D_eq, pi1D_eq]
      linarith [mul_le_mul_of_nonneg_left (hphi_le s') hm1.le]
    · have hDU := hBR .D
      rcases le_or_gt (P.ubar - (P.c - P.gam) * s') 0 with hxn | hxp
      · simp only [firmProfit] at hDU
        rw [prof_zero P hu s' _ hxn, prof_zero P hu s' _ hxn, prof0 P hu] at hDU
        linarith
      · have hx2 : P.ubar - (P.c - P.gam) * s' ≤ 2 * P.ubar := by
          linarith [mul_nonneg hk.le hs']
        simp only [firmProfit] at hDU
        rw [prof_eq P hu s' _ hxp.le hx2, prof_eq P hu s' _ hxp.le hx2, prof0 P hu] at hDU
        obtain ⟨x, hxd⟩ : ∃ x, P.ubar - (P.c - P.gam) * s' = x := ⟨_, rfl⟩
        rw [hxd] at hDU hxp
        have hT3' : P.m2 / (4 * P.ubar) * (P.ubar ^ 2 - xbar ^ 2)
            = P.m2 * (P.ubar / 4) - P.m2 * (xbar ^ 2 / (4 * P.ubar)) := by
          field_simp; try ring
        rw [hT3'] at hT3
        have hq : P.m2 * (xbar ^ 2 / (4 * P.ubar)) ≤ P.m2 * (x ^ 2 / (4 * P.ubar)) := by
          linarith
        have hq2 := le_of_mul_le_mul_left hq hm2
        rw [div_le_div_iff_of_pos_right (by linarith)] at hq2
        have hxb : xbar ≤ x := by
          by_contra h; push_neg at h
          linarith [mul_self_lt_mul_self hxp.le h]
        have hs'eq : (P.ubar - x) / (P.c - P.gam) = s' := by
          rw [← hxd]; exact back_aux _ _ _ hk'
        have hFx := hF x
        rw [hs'eq] at hFx
        rw [pi1U_eq P s' (by rw [hxd]; exact hxp.le), hFx, hpiD]
        exact quad_le a β _ xbar ha hC hg x hxb
    · rw [pi1D_eq]
      simp only [pi1]
      have : 0 ≤ P.m1 * phi P (saStar P) := by rw [hphiS]; exact (mul_pos hm1 hpos).le
      linarith
  refine ⟨⟨saStar P, hbase⟩, ?_⟩
  intro s1 hs1
  have hs1e : s1 = saStar P := by
    by_contra hne
    have h1 := hs1.2.2 (saStar P) .D hse.le hDBR
    rw [pi1D_eq, pi1D_eq] at h1
    linarith [mul_lt_mul_of_pos_left (hphi_lt s1 hne) hm1]
  subst hs1e
  simp only [show (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
      ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam))) = saStar P from rfl]
  have hsum := pi12D_eq P (saStar P)
  have hTh := Th_eq P (saStar P)
  have hgap : pi1 P (saStar P) .D + pi2 P (saStar P) .D < Th P (saStar P) := by
    have h0 := hphi_lt 0 (ne_of_lt hse)
    rw [hsum, hTh]
    linarith [mul_lt_mul_of_pos_left h0 hm2]
  -- Nash bargaining
  have hfeas_val : ∀ q ∈ BargFeasible P (pi1 P (saStar P) .D) (pi2 P (saStar P) .D),
      0 ≤ Pi1 P q.1 q.2 - pi1 P (saStar P) .D ∧
      nashProduct P (pi1 P (saStar P) .D) (pi2 P (saStar P) .D) q
        = (Pi1 P q.1 q.2 - pi1 P (saStar P) .D) * (Pi1 P q.1 q.2 - pi1 P (saStar P) .D) ∧
      2 * (Pi1 P q.1 q.2 - pi1 P (saStar P) .D)
        = Th P q.1 - pi1 P (saStar P) .D - pi2 P (saStar P) .D ∧
      0 ≤ q.1 := by
    intro q hq
    obtain ⟨h0, h1, h2, h3⟩ := hq
    refine ⟨by linarith, ?_, ?_, h0⟩
    · unfold nashProduct; rw [← h3]
    · have : Pi1 P q.1 q.2 + Pi2 P q.1 q.2 = Th P q.1 := by unfold Pi1 Pi2 Th; ring
      linarith
  obtain ⟨w, hwd⟩ : ∃ w, (Th P (saStar P) - pi1 P (saStar P) .D - pi2 P (saStar P) .D) / 2 = w :=
    ⟨_, rfl⟩
  have hw : 0 < w := by rw [← hwd]; linarith
  let th := (pi1 P (saStar P) .U - pi2 P (saStar P) .U - pi1 P (saStar P) .D
    + pi2 P (saStar P) .D) / 2
  have hstarF : ((saStar P, th) : ℝ × ℝ) ∈
      BargFeasible P (pi1 P (saStar P) .D) (pi2 P (saStar P) .D) := by
    have e1 : Pi1 P (saStar P) th - pi1 P (saStar P) .D = w := by
      rw [← hwd]; simp only [Pi1, Th, th]; ring
    have e2 : Pi2 P (saStar P) th - pi2 P (saStar P) .D = w := by
      rw [← hwd]; simp only [Pi2, Th, th]; ring
    refine ⟨hse.le, ?_, ?_, ?_⟩
    · show pi1 P (saStar P) .D ≤ Pi1 P (saStar P) th; linarith
    · show pi2 P (saStar P) .D ≤ Pi2 P (saStar P) th; linarith
    · show Pi1 P (saStar P) th - pi1 P (saStar P) .D = Pi2 P (saStar P) th - pi2 P (saStar P) .D
      rw [e1, e2]
  have hstarN : nashProduct P (pi1 P (saStar P) .D) (pi2 P (saStar P) .D) (saStar P, th)
      = w * w := by
    obtain ⟨-, hn, h2, -⟩ := hfeas_val _ hstarF
    rw [hn]
    have : Pi1 P (saStar P, th).1 (saStar P, th).2 - pi1 P (saStar P) .D = w := by
      rw [← hwd]; linarith
    rw [this]
  have hThle : ∀ s, Th P s ≤ Th P (saStar P) := by
    intro s; rw [Th_eq, Th_eq]
    exact mul_le_mul_of_nonneg_left (hphi_le s) (add_pos hm1 hm2).le
  refine ⟨⟨(saStar P, th), hstarF, ?_⟩, ?_, hgap, ?_⟩
  · intro q' hq'
    obtain ⟨hv0, hn, h2, -⟩ := hfeas_val q' hq'
    rw [hn, hstarN]
    have hle : Pi1 P q'.1 q'.2 - pi1 P (saStar P) .D ≤ w := by
      have := hThle q'.1
      rw [← hwd]; linarith
    exact mul_self_le_mul_self hv0 hle
  · intro q hq
    obtain ⟨hqF, hqmax⟩ := hq
    obtain ⟨hv0, hn, h2, hq0⟩ := hfeas_val q hqF
    have hm := hqmax _ hstarF
    rw [hn, hstarN] at hm
    have hwv : w ≤ Pi1 P q.1 q.2 - pi1 P (saStar P) .D := by
      by_contra h; push_neg at h
      exact absurd hm (not_le.mpr (mul_self_lt_mul_self hv0 h))
    by_contra hne
    have hlt := hphi_lt q.1 hne
    have : Th P q.1 < Th P (saStar P) := by
      rw [Th_eq, Th_eq]; exact mul_lt_mul_of_pos_left hlt (add_pos hm1 hm2)
    have : Th P (saStar P) ≤ Th P q.1 := by
      rw [← hwd] at hwv; linarith
    linarith
  · simp only [emissions, sales]
    rw [margin_of hy0, hm0]
    have key : (P.b - saStar P) * (P.m1 * (P.ubar - (P.c - P.gam) * saStar P) / (2 * P.ubar))
        + P.b * (P.m2 * P.ubar / (2 * P.ubar))
        - (P.b - saStar P) * (P.m1 * (P.ubar - (P.c - P.gam) * saStar P) / (2 * P.ubar)
          + P.m2 * (P.ubar - (P.c - P.gam) * saStar P) / (2 * P.ubar))
        = P.m2 * saStar P * (P.b * (P.c - P.gam) + (P.ubar - (P.c - P.gam) * saStar P))
          / (2 * P.ubar) := by
      field_simp; try ring
    have : 0 < P.m2 * saStar P * (P.b * (P.c - P.gam) + (P.ubar - (P.c - P.gam) * saStar P))
        / (2 * P.ubar) :=
      div_pos (mul_pos (mul_pos hm2 hse) (by linarith [mul_nonneg hb hk.le])) (by linarith)
    linarith

end CE3Aux

open CurbEmissions.ExactStandard in
theorem solution (P : Params) (hP : Standing P) (xbar : ℝ)
    (hx : IsGreatest (xbarEqSet P) xbar) (hc : Cond1 P xbar) :
    (∃ s1, IsBaseEq P s1 .D) ∧
    ∀ s1, IsBaseEq P s1 .D →
      let D1 := pi1 P s1 .D
      let D2 := pi2 P s1 .D
      let se := (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
                  ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)))
      (NBS P D1 D2).Nonempty ∧
      (∀ q ∈ NBS P D1 D2, q.1 = se) ∧
      D1 + D2 < Th P se ∧
      emissions P se .U < emissions P s1 .D := by
  exact CE3Aux.main P hP xbar hx hc

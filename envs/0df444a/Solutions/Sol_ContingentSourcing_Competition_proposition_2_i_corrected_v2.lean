-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_2_i_corrected_v2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:17:11.200062+00:00
-- url     : https://prove2.me/submissions/4f1a6e3d-867a-4bd4-9d78-018eef537a7b

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

namespace CSProp2V

/-- Supplier U's payoff at ρ = 1 as a function of (w_U, w_R, w_E). -/
noncomputable def Uf (P : Params) (u r e : ℝ) : ℝ :=
  if r ≤ u then 0
  else if P.P1 * u + (1 - P.P1) * e ≤ r then (P.P1 * u - P.cU) * ((P.m - u) / 2)
  else (P.P1 * u - P.cU) * ((r - u) / (2 * (1 - P.P1)))

/-- Supplier R's payoff at ρ = 1 as a function of (w_U, w_R, w_E). -/
noncomputable def Rf (P : Params) (u r e : ℝ) : ℝ :=
  if r ≤ u then (r - P.cR) * ((P.m - r) / 2)
  else if P.P1 * u + (1 - P.P1) * e ≤ r then (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2)
  else (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1)))

lemma eta1_one (P : Params) (w : Prices) : P.eta1 1 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by
  simp [Params.eta1, Params.PB, Params.PG, Params.P0G, Params.P0]

lemma eta2_eq (P : Params) (w : Prices) : P.eta2 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by
  simp [Params.eta2, Params.P0]

lemma payU_eq (P : Params) (w : Prices) : P.payU 1 w = Uf P w.wU w.wR w.wE := by
  unfold Params.payU Params.order Uf
  rw [eta1_one, eta2_eq]
  split_ifs with h1 h2 h3
  · simp [Params.orderIV]
  · simp [Params.orderI]
  · exfalso; push_neg at h2; linarith
  · simp [Params.orderIII, Params.P0]; try ring

lemma payR_eq (P : Params) (w : Prices) : P.payR 1 w = Rf P w.wU w.wR w.wE := by
  unfold Params.payR Params.order Rf
  rw [eta1_one, eta2_eq]
  split_ifs with h1 h2 h3
  · simp [Params.orderIV]
  · simp [Params.orderI, Params.PB, Params.P0]; try ring
  · exfalso; push_neg at h2; linarith
  · simp [Params.orderIII, Params.P0]; try ring

lemma devU (P : Params) (w : Prices) (u : ℝ) : P.payU 1 ⟨u, w.wR, w.wE⟩ = Uf P u w.wR w.wE :=
  payU_eq P _
lemma devR (P : Params) (w : Prices) (r e : ℝ) : P.payR 1 ⟨w.wU, r, e⟩ = Rf P w.wU r e :=
  payR_eq P _

lemma Uf_IV (P : Params) (u r e : ℝ) (h : r ≤ u) : Uf P u r e = 0 := by unfold Uf; rw [if_pos h]
lemma Uf_I (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : P.P1 * u + (1 - P.P1) * e ≤ r) :
    Uf P u r e = (P.P1 * u - P.cU) * ((P.m - u) / 2) := by
  unfold Uf; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma Uf_M (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : r < P.P1 * u + (1 - P.P1) * e) :
    Uf P u r e = (P.P1 * u - P.cU) * ((r - u) / (2 * (1 - P.P1))) := by
  unfold Uf; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]
lemma Rf_IV (P : Params) (u r e : ℝ) (h : r ≤ u) : Rf P u r e = (r - P.cR) * ((P.m - r) / 2) := by
  unfold Rf; rw [if_pos h]
lemma Rf_I (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : P.P1 * u + (1 - P.P1) * e ≤ r) :
    Rf P u r e = (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2) := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma Rf_M (P : Params) (u r e : ℝ) (h1 : u < r) (h2 : r < P.P1 * u + (1 - P.P1) * e) :
    Rf P u r e = (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]

lemma UI_diff (P : Params) (x y : ℝ) :
    (P.P1 * y - P.cU) * ((P.m - y) / 2) - (P.P1 * x - P.cU) * ((P.m - x) / 2)
      = (y - x) * (P.P1 * P.m + P.cU - P.P1 * (x + y)) / 2 := by ring

/-- U's payoff never exceeds the contingent formula at the same price. -/
lemma Uf_le_UI (P : Params) (hP : P.Standing) (u r e : ℝ) (hu : P.cU ≤ P.P1 * u) (hum : u ≤ P.m)
    (he : e ≤ P.m) : Uf P u r e ≤ (P.P1 * u - P.cU) * ((P.m - u) / 2) := by
  have hq : 0 < 1 - P.P1 := by linarith [hP.2.2.1]
  unfold Uf
  split_ifs with h1 h2
  · exact mul_nonneg (by linarith) (by linarith)
  · exact le_rfl
  · push_neg at h1 h2
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith [mul_le_mul_of_nonneg_left he hq.le]

/-- Facts implied by c_R > ψ_2 (in cleared form H2). -/
lemma facts (P : Params) (hP : P.Standing)
    (H2 : P.P1 * (1 - P.P1) * P.m + 2 * P.cU < P.P1 * (3 - P.P1) * P.cR) :
    P.cU < P.P1 * P.m ∧ (2 - P.P1) * P.cU < P.P1 * ((1 - P.P1) * P.m + P.cR) ∧
    2 * P.cU < P.P1 * (P.m + P.cR) ∧ P.cU < P.P1 * P.cR := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  have hq : 0 < 1 - P.P1 := by linarith
  have t1 := mul_nonneg (mul_nonneg hq.le (by linarith : (0:ℝ) ≤ 4 - P.P1)) (sub_nonneg.mpr hcm)
  have t2 := mul_nonneg (mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ 2 - P.P1)) (sub_nonneg.mpr hrm)
  have t3 := mul_nonneg hq.le (sub_nonneg.mpr hcm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc; push_neg at hc
    have heq : P.cU = P.P1 * P.m := le_antisymm hcm hc
    rw [heq] at H2
    have : P.P1 * ((3 - P.P1) * P.m) < P.P1 * ((3 - P.P1) * P.cR) := by linarith
    have := lt_of_mul_lt_mul_left this hp0.le
    have := lt_of_mul_lt_mul_left this (by linarith : (0:ℝ) ≤ 3 - P.P1)
    linarith
  · have : (3 - P.P1) * ((2 - P.P1) * P.cU) < (3 - P.P1) * (P.P1 * ((1 - P.P1) * P.m + P.cR)) := by
      linarith
    exact lt_of_mul_lt_mul_left this (by linarith)
  · linarith
  · have : (3 - P.P1) * P.cU < (3 - P.P1) * (P.P1 * P.cR) := by linarith
    exact lt_of_mul_lt_mul_left this (by linarith)

/-- Step A: no Nash equilibrium has R undercutting U. -/
lemma notIV (P : Params) (hP : P.Standing) (hea : 2 * P.cU < P.P1 * (P.m + P.cR))
    (h3 : (2 - P.P1) * P.cU < P.P1 * ((1 - P.P1) * P.m + P.cR))
    (w : Prices) (hN : P.IsNash 1 w) : w.wU < w.wR := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  have hwRm : w.wR ≤ P.m := hR2.trans hR3
  by_contra hIV; push_neg at hIV
  have curU : P.payU 1 w = 0 := by rw [payU_eq]; exact Uf_IV P _ _ _ hIV
  have curR : P.payR 1 w = (w.wR - P.cR) * ((P.m - w.wR) / 2) := by
    rw [payR_eq]; exact Rf_IV P _ _ _ hIV
  by_cases ha : P.cU < P.P1 * w.wR
  · set u' := (P.cU / P.P1 + w.wR) / 2 with hu'
    have hpu : 2 * (P.P1 * u') = P.cU + P.P1 * w.wR := by rw [hu']; field_simp
    have hu1 : P.cU < P.P1 * u' := by linarith
    have hu2 : u' < w.wR := by
      have : P.P1 * u' < P.P1 * w.wR := by linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have hdev := hUo u' ⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩
    rw [devU, curU] at hdev
    by_cases h2 : P.P1 * u' + (1 - P.P1) * w.wE ≤ w.wR
    · rw [Uf_I P _ _ _ hu2 h2] at hdev
      have := mul_pos (by linarith : 0 < P.P1 * u' - P.cU) (by linarith : 0 < (P.m - u') / 2)
      linarith
    · push_neg at h2
      rw [Uf_M P _ _ _ hu2 h2] at hdev
      have := mul_pos (by linarith : 0 < P.P1 * u' - P.cU)
        (div_pos (by linarith : 0 < w.wR - u') (by linarith : (0:ℝ) < 2 * (1 - P.P1)))
      linarith
  · push_neg at ha
    have hmid' : w.wR < (P.m + P.cR) / 2 := by
      have : P.P1 * w.wR < P.P1 * ((P.m + P.cR) / 2) := by linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    rcases hIV.lt_or_eq with hlt | heq
    · set r' := min w.wU ((P.m + P.cR) / 2) with hr'
      have hr'1 : w.wR < r' := lt_min hlt hmid'
      have hr'2 : r' ≤ w.wU := min_le_left _ _
      have hr'3 : r' ≤ (P.m + P.cR) / 2 := min_le_right _ _
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_IV P _ _ _ hr'2] at hdev
      have : 0 < (r' - w.wR) * (P.m + P.cR - r' - w.wR) := mul_pos (by linarith) (by linarith)
      linarith
    · have hpw : P.P1 * w.wU = P.cU := by
        have h' := hU1'; rw [← heq] at h' ⊢; linarith
      set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
      set r' := (η + P.cR) / 2 with hr'
      have hwm : w.wU < P.m := by
        by_contra hc; push_neg at hc
        have : P.P1 * P.m ≤ P.P1 * w.wU := mul_le_mul_of_nonneg_left hc hp0.le
        have : P.cR ≤ P.m := hrm
        linarith
      have hr'1 : w.wU < r' := by
        have : P.P1 * ((2 - P.P1) * w.wU) < P.P1 * ((1 - P.P1) * P.m + P.cR) := by
          have : (2 - P.P1) * (P.P1 * w.wU) < P.P1 * ((1 - P.P1) * P.m + P.cR) := by rw [hpw]; exact h3
          linarith
        have := lt_of_mul_lt_mul_left this hp0.le
        rw [hr', hη]; linarith
      have hwη : w.wU < η := by rw [hη]; linarith [mul_pos hq (sub_pos.mpr hwm)]
      have hcη : P.cR < η := by linarith
      have hr'2 : r' < η := by rw [hr']; linarith
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_M P _ _ _ hr'1 (by rw [← hη]; linarith)] at hdev
      have e1 : (w.wR - P.cR) * ((P.m - w.wR) / 2) =
          (w.wU - P.cR) * (η - w.wU) / (2 * (1 - P.P1)) := by
        have : η - w.wU = (1 - P.P1) * (P.m - w.wU) := by rw [hη]; ring
        rw [heq, this]; field_simp
      have e2 : (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) =
          (r' - P.cR) * (η - r') / (2 * (1 - P.P1)) := by rw [hη]; ring
      rw [e1, e2, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have : (r' - P.cR) * (η - r') - (w.wU - P.cR) * (η - w.wU) = (w.wU - r') ^ 2 := by
        rw [hr']; ring
      have : 0 < (w.wU - r') ^ 2 := by
        have : w.wU - r' ≠ 0 := by linarith
        positivity
      linarith

/-- Step B: no Nash equilibrium has the buyer diversifying (case iii). -/
lemma notIII (P : Params) (hP : P.Standing)
    (H2 : P.P1 * (1 - P.P1) * P.m + 2 * P.cU < P.P1 * (3 - P.P1) * P.cR)
    (w : Prices) (hN : P.IsNash 1 w) (h1 : w.wU < w.wR) :
    P.P1 * w.wU + (1 - P.P1) * w.wE ≤ w.wR := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  have hwRm : w.wR ≤ P.m := hR2.trans hR3
  by_contra h2; push_neg at h2
  set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
  have hηE : P.P1 * w.wU + (1 - P.P1) * w.wE ≤ η := by
    rw [hη]; linarith [mul_le_mul_of_nonneg_left hR3 hq.le]
  have curU : P.payU 1 w = (P.P1 * w.wU - P.cU) * ((w.wR - w.wU) / (2 * (1 - P.P1))) := by
    rw [payU_eq]; exact Uf_M P _ _ _ h1 h2
  have curR : P.payR 1 w = (w.wR - P.cR) * (η - w.wR) / (2 * (1 - P.P1)) := by
    rw [payR_eq, Rf_M P _ _ _ h1 h2, hη]; ring
  have hcη : P.cR < η := by linarith
  have hηm : η ≤ P.m := by rw [hη]; linarith [mul_nonneg hp0.le (sub_nonneg.mpr hU2)]
  -- B1: R sits at the vertex of its parabola
  have B1 : 2 * w.wR = η + P.cR := by
    set r' := (η + P.cR) / 2 with hr'
    rcases le_or_gt r' w.wU with hle | hgt
    · exfalso
      have hdev := hRo w.wU P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_IV P _ _ _ le_rfl] at hdev
      have e : (w.wU - P.cR) * ((P.m - w.wU) / 2) = (w.wU - P.cR) * (η - w.wU) / (2 * (1 - P.P1)) := by
        have : η - w.wU = (1 - P.P1) * (P.m - w.wU) := by rw [hη]; ring
        rw [this]; field_simp
      rw [e, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e2 : (w.wU - P.cR) * (η - w.wU) - (w.wR - P.cR) * (η - w.wR)
          = (w.wR - w.wU) * (w.wU + w.wR - 2 * r') := by rw [hr']; ring
      have : 0 < (w.wR - w.wU) * (w.wU + w.wR - 2 * r') := mul_pos (by linarith) (by linarith)
      linarith
    · by_contra hne
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_M P _ _ _ hgt (by rw [← hη]; linarith)] at hdev
      have e : (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) =
          (r' - P.cR) * (η - r') / (2 * (1 - P.P1)) := by rw [hη]; ring
      rw [e, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e2 : (r' - P.cR) * (η - r') - (w.wR - P.cR) * (η - w.wR) = (w.wR - r') ^ 2 := by
        rw [hr']; ring
      have : 0 < (w.wR - r') ^ 2 := by
        have : w.wR - r' ≠ 0 := by intro h0; apply hne; linarith
        positivity
      linarith
  -- B2: U's price is at least c_R (else R prefers contingent sourcing)
  have B2 : P.cR ≤ w.wU := by
    by_contra hc; push_neg at hc
    set e' := (P.m + P.cR) / 2 with he'
    have hreg1 : w.wU < e' := by linarith
    have hreg2 : P.P1 * w.wU + (1 - P.P1) * e' ≤ e' := by
      have := mul_le_mul_of_nonneg_left hreg1.le hp0.le; linarith
    have hdev := hRo e' e' ⟨by linarith, le_rfl, by linarith⟩
    rw [devR, curR, Rf_I P _ _ _ hreg1 hreg2] at hdev
    have hx : 0 ≤ η - P.cR := by linarith
    have hy : η - P.cR < (1 - P.P1) * (P.m - P.cR) := by
      rw [hη]; linarith [mul_lt_mul_of_pos_left hc hp0]
    have hsq := mul_self_lt_mul_self hx hy
    have e1 : (w.wR - P.cR) * (η - w.wR) = (η - P.cR) * (η - P.cR) / 4 := by
      have : w.wR = (η + P.cR) / 2 := by linarith
      rw [this]; ring
    rw [e1] at hdev
    have e2 : (1 - P.P1) * (e' - P.cR) * ((P.m - e') / 2) =
        ((1 - P.P1) * (P.m - P.cR)) * ((1 - P.P1) * (P.m - P.cR)) / (8 * (1 - P.P1)) := by
      rw [he']; field_simp; ring
    rw [e2] at hdev
    have : (η - P.cR) * (η - P.cR) / 4 / (2 * (1 - P.P1)) =
        (η - P.cR) * (η - P.cR) / (8 * (1 - P.P1)) := by field_simp; ring
    rw [this, div_le_div_iff_of_pos_right (by linarith)] at hdev
    linarith
  -- B3: U sits at the vertex of its parabola
  have B3 : 2 * (P.P1 * w.wU) = P.cU + P.P1 * w.wR := by
    set v := (P.cU / P.P1 + w.wR) / 2 with hv
    have hpv : 2 * (P.P1 * v) = P.cU + P.P1 * w.wR := by rw [hv]; field_simp
    set lam := (w.wR - (1 - P.P1) * w.wE) / P.P1 with hlam
    have hpl : P.P1 * lam = w.wR - (1 - P.P1) * w.wE := by rw [hlam]; field_simp
    have hlw : lam < w.wU := by
      have : P.P1 * lam < P.P1 * w.wU := by linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have hpU : P.P1 * w.wU < P.P1 * w.wR := mul_lt_mul_of_pos_left h1 hp0
    set H := fun u : ℝ => (P.P1 * u - P.cU) * (w.wR - u) with hH
    have curU' : P.payU 1 w = H w.wU / (2 * (1 - P.P1)) := by rw [curU, hH]; ring
    rcases le_or_gt (P.P1 * v) (P.P1 * lam) with hle | hgt
    · exfalso
      have hdev := hUo lam ⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩
      rw [devU, curU', Uf_I P _ _ _ (by linarith) (by linarith)] at hdev
      have hle2 : H lam / (2 * (1 - P.P1)) ≤ (P.P1 * lam - P.cU) * ((P.m - lam) / 2) := by
        rw [hH]; simp only
        rw [div_le_iff₀ (by linarith)]
        have hwl : w.wR - lam = (1 - P.P1) * (w.wE - lam) := by linarith
        rw [hwl]
        have : 0 ≤ P.P1 * lam - P.cU := by linarith
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (by linarith : w.wE - lam ≤ P.m - lam) hq.le) this
        nlinarith
      have e2 : H lam - H w.wU = (w.wU - lam) * (P.P1 * (w.wU + lam) - 2 * (P.P1 * v)) := by
        rw [hH]; simp only; linear_combination (w.wU - lam) * hpv
      have : 0 < (w.wU - lam) * (P.P1 * (w.wU + lam) - 2 * (P.P1 * v)) := by
        apply mul_pos (by linarith)
        have := mul_lt_mul_of_pos_left hlw hp0
        linarith
      have : H w.wU / (2 * (1 - P.P1)) < H lam / (2 * (1 - P.P1)) :=
        div_lt_div_of_pos_right (by linarith) (by linarith)
      linarith
    · by_contra hne
      have hvl : lam < v := lt_of_mul_lt_mul_left hgt hp0.le
      have hvw : v < w.wR := by
        have : P.P1 * v < P.P1 * w.wR := by linarith
        exact lt_of_mul_lt_mul_left this hp0.le
      have hdev := hUo v ⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩
      rw [devU, curU', Uf_M P _ _ _ hvw (by linarith)] at hdev
      have e : (P.P1 * v - P.cU) * ((w.wR - v) / (2 * (1 - P.P1))) = H v / (2 * (1 - P.P1)) := by
        rw [hH]; ring
      rw [e, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e2 : H v - H w.wU = P.P1 * (w.wU - v) ^ 2 := by
        rw [hH]; simp only; linear_combination (w.wU - v) * hpv
      have : 0 < P.P1 * (w.wU - v) ^ 2 := by
        have : w.wU - v ≠ 0 := by
          intro h0; apply hne; have : w.wU = v := by linarith
          rw [this]; exact hpv
        positivity
      linarith
  -- B4: contradiction with c_R > ψ_2
  have e3 : (4 - P.P1) * (P.P1 * w.wU) = 2 * P.cU + P.P1 * (1 - P.P1) * P.m + P.P1 * P.cR := by
    linear_combination 2 * B3 + P.P1 * B1 + P.P1 * hη
  have := mul_le_mul_of_nonneg_left B2 (by nlinarith : (0:ℝ) ≤ (4 - P.P1) * P.P1)
  linarith

/-- Step C: Nash equilibria with contingent sourcing. -/
lemma regionI (P : Params) (hP : P.Standing) (hac : P.cU < P.P1 * P.cR)
    (w : Prices) (hN : P.IsNash 1 w) (h1 : w.wU < w.wR)
    (h2 : P.P1 * w.wU + (1 - P.P1) * w.wE ≤ w.wR) :
    2 * w.wE = P.m + P.cR ∧ w.wU ≤ P.cR ∧
    (2 * (P.P1 * w.wU) = P.P1 * P.m + P.cU ∨
      (2 * (P.P1 * w.wU) < P.P1 * P.m + P.cU ∧ w.wR = P.P1 * w.wU + (1 - P.P1) * w.wE)) := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  have hwRm : w.wR ≤ P.m := hR2.trans hR3
  have curU : P.payU 1 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) := by
    rw [payU_eq]; exact Uf_I P _ _ _ h1 h2
  have curR : P.payR 1 w = (1 - P.P1) * (w.wE - P.cR) * ((P.m - w.wE) / 2) := by
    rw [payR_eq]; exact Rf_I P _ _ _ h1 h2
  set e' := (P.m + P.cR) / 2 with he'
  have hvert : ∀ e : ℝ, (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2) =
      (1 - P.P1) * (e' - P.cR) * ((P.m - e') / 2) - (1 - P.P1) * (e - e') ^ 2 / 2 := by
    intro e; rw [he']; ring
  -- C0: U's price is below e'
  have C0 : w.wU < e' := by
    by_contra hc; push_neg at hc
    have hEe : e' < w.wE := by linarith
    have hdev := hRo e' P.m ⟨by linarith, by linarith, le_rfl⟩
    rw [devR, curR, Rf_IV P _ _ _ hc] at hdev
    rw [hvert w.wE] at hdev
    have e2 : (e' - P.cR) * ((P.m - e') / 2) = (e' - P.cR) * ((P.m - e') / 2) := rfl
    have hpos : 0 < (e' - P.cR) * ((P.m - e') / 2) := by
      apply mul_pos <;> linarith
    have : (1 - P.P1) * (e' - P.cR) * ((P.m - e') / 2) < (e' - P.cR) * ((P.m - e') / 2) := by
      have := mul_lt_mul_of_pos_right (by linarith : 1 - P.P1 < 1) hpos
      linarith
    have : 0 ≤ (1 - P.P1) * (w.wE - e') ^ 2 / 2 := by positivity
    linarith
  have hreg2 : P.P1 * w.wU + (1 - P.P1) * e' ≤ e' := by
    have := mul_le_mul_of_nonneg_left C0.le hp0.le; linarith
  -- C1: w_E = e'
  have C1 : 2 * w.wE = P.m + P.cR := by
    by_contra hne
    have hdev := hRo e' e' ⟨by linarith, le_rfl, by linarith⟩
    rw [devR, curR, Rf_I P _ _ _ C0 hreg2, hvert w.wE] at hdev
    have : 0 < (1 - P.P1) * (w.wE - e') ^ 2 / 2 := by
      have : w.wE - e' ≠ 0 := by intro h0; apply hne; linarith
      positivity
    linarith
  have curR' : P.payR 1 w = (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 := by
    rw [curR]; have : w.wE = e' := by linarith
    rw [this, he']; ring
  -- C2: U's price is at most c_R
  have C2 : w.wU ≤ P.cR := by
    by_contra hc; push_neg at hc
    set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
    have hcm' : P.cR < P.m := by linarith
    have hηc : P.cR < η := by
      have a1 := mul_lt_mul_of_pos_left hc hp0
      have a2 := mul_lt_mul_of_pos_left hcm' hq
      rw [hη]; linarith
    have hηm : η ≤ P.m := by rw [hη]; linarith [mul_nonneg hp0.le (sub_nonneg.mpr hU2)]
    set r' := (η + P.cR) / 2 with hr'
    rcases lt_or_ge w.wU r' with hlt | hge
    · -- R moves to the vertex of its diversification parabola
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR', Rf_M P _ _ _ hlt (by rw [← hη]; linarith)] at hdev
      have e : (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) =
          (η - P.cR) * (η - P.cR) / (8 * (1 - P.P1)) := by rw [hr', hη]; field_simp; ring
      rw [e] at hdev
      have hx : 0 ≤ (1 - P.P1) * (P.m - P.cR) := by positivity
      have hy : (1 - P.P1) * (P.m - P.cR) < η - P.cR := by
        rw [hη]; linarith [mul_lt_mul_of_pos_left hc hp0]
      have hsq := mul_self_lt_mul_self hx hy
      have e2 : (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 =
          ((1 - P.P1) * (P.m - P.cR)) * ((1 - P.P1) * (P.m - P.cR)) / (8 * (1 - P.P1)) := by
        field_simp
      rw [e2, div_le_div_iff_of_pos_right (by linarith)] at hdev
      linarith
    · -- R undercuts at w_U
      have hdev := hRo w.wU P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR', Rf_IV P _ _ _ le_rfl] at hdev
      set t := w.wU - P.cR with ht
      set z := P.m - P.cR with hz
      have hA : 0 ≤ (2 - P.P1) * t - (1 - P.P1) * z := by rw [ht, hz]; rw [hr', hη] at hge; linarith
      have hB : 0 < z - (2 - P.P1) * t := by
        have : 2 * t < z := by rw [ht, hz]; linarith
        have := mul_le_mul_of_nonneg_right (by linarith : 1 - P.P1 ≤ 1) (by linarith : (0:ℝ) ≤ t)
        linarith
      have iden : (2 - P.P1) ^ 2 * (4 * t * (z - t) - (1 - P.P1) * z ^ 2) =
          4 * ((2 - P.P1) * t - (1 - P.P1) * z) * (z - (2 - P.P1) * t)
          + (1 - P.P1) * P.P1 * (4 - P.P1) * z ^ 2 := by ring
      have hz0 : 0 < z := by rw [hz]; linarith
      have hpos : 0 < (2 - P.P1) ^ 2 * (4 * t * (z - t) - (1 - P.P1) * z ^ 2) := by
        rw [iden]
        have := mul_nonneg hA hB.le
        have : 0 < (1 - P.P1) * P.P1 * (4 - P.P1) * z ^ 2 := by
          have : (0:ℝ) < 4 - P.P1 := by linarith
          positivity
        linarith
      have h4 : 0 < 4 * t * (z - t) - (1 - P.P1) * z ^ 2 := by
        by_contra hh; push_neg at hh
        have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0:ℝ) ≤ (2 - P.P1) ^ 2) hh
        linarith
      have e3 : (w.wU - P.cR) * ((P.m - w.wU) / 2) = t * (z - t) / 2 := by rw [ht, hz]; ring
      rw [e3] at hdev
      have e4 : (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 = (1 - P.P1) * z ^ 2 / 8 := by rw [hz]
      rw [e4] at hdev
      linarith
  refine ⟨C1, C2, ?_⟩
  -- C3: U's price is ψ₁ or the limit price
  rcases lt_trichotomy (2 * (P.P1 * w.wU)) (P.P1 * P.m + P.cU) with hlt | heq | hgt
  · right
    refine ⟨hlt, ?_⟩
    by_contra hne
    have hlt2 : P.P1 * w.wU + (1 - P.P1) * w.wE < w.wR := lt_of_le_of_ne h2 (fun h0 => hne h0.symm)
    set t := min ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((w.wR - (1 - P.P1) * w.wE) / P.P1) with htd
    have ht1 : 2 * (P.P1 * t) ≤ P.P1 * P.m + P.cU := by
      have := min_le_left ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((w.wR - (1 - P.P1) * w.wE) / P.P1)
      rw [← htd, le_div_iff₀ (by positivity)] at this; linarith
    have ht2 : P.P1 * t ≤ w.wR - (1 - P.P1) * w.wE := by
      have := min_le_right ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((w.wR - (1 - P.P1) * w.wE) / P.P1)
      rw [← htd, le_div_iff₀ hp0] at this; linarith
    have ht3 : w.wU < t := by
      rw [htd]; apply lt_min
      · rw [lt_div_iff₀ (by positivity)]; linarith
      · rw [lt_div_iff₀ hp0]; linarith
    have ht4 : t < w.wR := by
      rcases lt_or_eq_of_le hR2 with hRE | hRE
      · have : P.P1 * t < P.P1 * w.wR := by linarith [mul_lt_mul_of_pos_left hRE hq]
        exact lt_of_mul_lt_mul_left this hp0.le
      · -- w_R = w_E = e' > ψ₁ ≥ t
        have : P.P1 * t < P.P1 * w.wR := by
          have h0 : 2 * w.wR = P.m + P.cR := by rw [hRE]; exact C1
          have h' : 2 * (P.P1 * w.wR) = P.P1 * P.m + P.P1 * P.cR := by linear_combination P.P1 * h0
          linarith
        exact lt_of_mul_lt_mul_left this hp0.le
    have htm : t ≤ P.m := by
      have : P.P1 * t ≤ P.P1 * P.m := by linarith
      exact le_of_mul_le_mul_left this hp0
    have hdev := hUo t ⟨by rw [div_le_iff₀ hp0]; linarith [mul_lt_mul_of_pos_left ht3 hp0], htm⟩
    rw [devU, curU, Uf_I P _ _ _ ht4 (by linarith)] at hdev
    have e := UI_diff P w.wU t
    have : 0 < (t - w.wU) * (P.P1 * P.m + P.cU - P.P1 * (w.wU + t)) :=
      mul_pos (by linarith) (by linarith [mul_pos hp0 (sub_pos.mpr ht3)])
    linarith
  · left; exact heq
  · exfalso
    set t := (P.P1 * P.m + P.cU) / (2 * P.P1) with htd
    have hpt : 2 * (P.P1 * t) = P.P1 * P.m + P.cU := by rw [htd]; field_simp
    have ht1 : t < w.wU := by
      have : P.P1 * t < P.P1 * w.wU := by linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have htm : t ≤ P.m := by
      have : P.P1 * t ≤ P.P1 * P.m := by linarith
      exact le_of_mul_le_mul_left this hp0
    have hdev := hUo t ⟨by rw [div_le_iff₀ hp0]; linarith, htm⟩
    rw [devU, curU, Uf_I P _ _ _ (by linarith) (by linarith [mul_lt_mul_of_pos_left ht1 hp0])] at hdev
    have e := UI_diff P w.wU t
    have : 0 < (w.wU - t) * (P.P1 * (w.wU + t) - (P.P1 * P.m + P.cU)) :=
      mul_pos (by linarith) (by linarith)
    linarith

lemma c_psi2 (P : Params) (hP : P.Standing) :
    P.psi2 < P.cR ↔ P.P1 * (1 - P.P1) * P.m + 2 * P.cU < P.P1 * (3 - P.P1) * P.cR := by
  have hp0 := hP.2.1; have hp1 := hP.2.2.1
  unfold Params.psi2 Params.P0
  rw [show (1 - P.P1 + 2) = 3 - P.P1 by ring, div_lt_iff₀ (by linarith)]
  have e : ((1 - P.P1) * P.m + 2 * P.cU / P.P1) * P.P1 = P.P1 * (1 - P.P1) * P.m + 2 * P.cU := by
    field_simp; try ring
  constructor
  · intro h1
    have := mul_lt_mul_of_pos_right h1 hp0
    linarith
  · intro h1
    have : ((1 - P.P1) * P.m + 2 * P.cU / P.P1) * P.P1 < (P.cR * (3 - P.P1)) * P.P1 := by linarith
    exact lt_of_mul_lt_mul_right this hp0.le

lemma c_psi1 (P : Params) (hP : P.Standing) :
    P.psi1 < P.cR ↔ P.P1 * P.m + P.cU < 2 * (P.P1 * P.cR) := by
  have hp0 := hP.2.1
  unfold Params.psi1
  rw [div_lt_iff₀ (by positivity)]; constructor <;> intro h <;> linarith

/-- R earns at most the contingent maximum against any U price u ≤ c_R. -/
lemma Rdev_bound (P : Params) (hP : P.Standing) (u r e : ℝ) (hu : u ≤ P.cR) (hr : P.cR ≤ r)
    (hre : r ≤ e) (he : e ≤ P.m) :
    Rf P u r e ≤ (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  have hq : 0 < 1 - P.P1 := by linarith
  have hmax : 0 ≤ (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 := by positivity
  unfold Rf
  split_ifs with g1 g2
  · have : r = P.cR := by linarith
    rw [this]; simp; exact hmax
  · have : (1 - P.P1) * (e - P.cR) * ((P.m - e) / 2) =
        (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 - (1 - P.P1) * (e - (P.m + P.cR) / 2) ^ 2 / 2 := by ring
    rw [this]
    have : 0 ≤ (1 - P.P1) * (e - (P.m + P.cR) / 2) ^ 2 / 2 := by positivity
    linarith
  · push_neg at g1 g2
    set η := P.P1 * u + (1 - P.P1) * P.m with hη
    have hηe : P.P1 * u + (1 - P.P1) * e ≤ η := by
      rw [hη]; linarith [mul_le_mul_of_nonneg_left he hq.le]
    have hx : 0 ≤ η - P.cR := by linarith
    have hy : η - P.cR ≤ (1 - P.P1) * (P.m - P.cR) := by
      rw [hη]; linarith [mul_le_mul_of_nonneg_left hu hp0.le]
    have hsq := mul_self_le_mul_self hx hy
    have e1 : (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) =
        (r - P.cR) * (η - r) / (2 * (1 - P.P1)) := by rw [hη]; ring
    rw [e1, div_le_iff₀ (by linarith)]
    have : (r - P.cR) * (η - r) ≤ (η - P.cR) * (η - P.cR) / 4 := by
      nlinarith [sq_nonneg (2 * r - η - P.cR)]
    have e2 : (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 * (2 * (1 - P.P1)) =
        ((1 - P.P1) * (P.m - P.cR)) * ((1 - P.P1) * (P.m - P.cR)) / 4 := by ring
    rw [e2]; linarith

lemma priceI_eq (P : Params) :
    P.priceI = ⟨if P.psi1 < P.cR then P.psi1 else P.cR,
      P.P1 * (if P.psi1 < P.cR then P.psi1 else P.cR) + (1 - P.P1) * ((P.m + P.cR) / 2),
      (P.m + P.cR) / 2⟩ := by
  unfold Params.priceI Params.P0; split_ifs <;> rfl

/-- The Table 2 profile, with w_R raised to c_R if needed, is a Nash equilibrium. -/
lemma w0_nash (P : Params) (hP : P.Standing)
    (H2 : P.P1 * (1 - P.P1) * P.m + 2 * P.cU < P.P1 * (3 - P.P1) * P.cR) (u0 : ℝ)
    (hu0 : (P.psi1 < P.cR ∧ u0 = P.psi1) ∨ (¬ P.psi1 < P.cR ∧ u0 = P.cR)) :
    P.IsNash 1 ⟨u0, max (P.P1 * u0 + (1 - P.P1) * ((P.m + P.cR) / 2)) P.cR, (P.m + P.cR) / 2⟩ := by
  obtain ⟨hk, h3, hea, hac⟩ := facts P hP H2
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  set e' := (P.m + P.cR) / 2 with he'
  set r0 := max (P.P1 * u0 + (1 - P.P1) * e') P.cR with hr0d
  have hpsi1 := c_psi1 P hP
  -- common facts: u0 ≤ c_R, 2 P1 u0 ≤ P1 m + cU, cU ≤ P1 u0, u0 < r0
  have hu0c : u0 ≤ P.cR := by
    rcases hu0 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact h.le
    · exact le_rfl
  have hu0p : 2 * (P.P1 * u0) ≤ P.P1 * P.m + P.cU := by
    rcases hu0 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · unfold Params.psi1; field_simp; linarith
    · have := mt hpsi1.mpr h; push_neg at this; linarith
  have hu0U : P.cU ≤ P.P1 * u0 := by
    rcases hu0 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · unfold Params.psi1; field_simp; linarith
    · linarith
  have hu0m : u0 ≤ P.m := le_trans hu0c hrm
  have hcm' : P.cR < P.m ∨ u0 < P.cR := by
    rcases hu0 with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · right; exact h
    · left
      have h2 := mt hpsi1.mpr h; push_neg at h2
      by_contra hc; push_neg at hc
      have hcr : P.cR = P.m := le_antisymm hrm hc
      have : P.P1 * P.cR = P.P1 * P.m := by rw [hcr]
      linarith
  have hr0a : P.P1 * u0 + (1 - P.P1) * e' ≤ r0 := le_max_left _ _
  have hr0b : P.cR ≤ r0 := le_max_right _ _
  have hu0r : u0 < r0 := by
    rcases hcm' with h | h
    · have : u0 < P.P1 * u0 + (1 - P.P1) * e' := by
        have := mul_lt_mul_of_pos_left (by linarith : u0 < e') hq; linarith
      linarith
    · linarith
  have hr0e : r0 ≤ e' := by
    have hue : u0 ≤ e' := by linarith
    have := mul_le_mul_of_nonneg_left hue hp0.le
    exact max_le (by linarith) (by linarith)
  have curU : P.payU 1 ⟨u0, r0, e'⟩ = (P.P1 * u0 - P.cU) * ((P.m - u0) / 2) := by
    rw [payU_eq]; exact Uf_I P _ _ _ hu0r hr0a
  have curR : P.payR 1 ⟨u0, r0, e'⟩ = (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 := by
    rw [payR_eq]; simp only; rw [Rf_I P _ _ _ hu0r hr0a, he']; ring
  refine ⟨⟨by rw [div_le_iff₀ hp0]; linarith, hu0m⟩, ⟨hr0b, hr0e, by linarith⟩, ?_, ?_⟩
  · intro r e ⟨g1, g2, g3⟩
    rw [devR, curR]
    exact Rdev_bound P hP u0 r e hu0c g1 g2 g3
  · intro u ⟨g1, g2⟩
    have g1' : P.cU ≤ P.P1 * u := by rw [div_le_iff₀ hp0] at g1; linarith
    rw [devU, curU]
    rcases hu0 with ⟨h, rfl⟩ | ⟨h, hcr⟩
    · -- (i-a): ψ₁ is U's unconstrained optimum
      refine (Uf_le_UI P hP u _ _ g1' g2 (by linarith)).trans ?_
      have e := UI_diff P u P.psi1
      have hp1s : 2 * (P.P1 * P.psi1) = P.P1 * P.m + P.cU := by unfold Params.psi1; field_simp
      have : 0 ≤ (P.psi1 - u) * (P.P1 * P.m + P.cU - P.P1 * (u + P.psi1)) := by
        have : P.P1 * P.m + P.cU - P.P1 * (u + P.psi1) = P.P1 * (P.psi1 - u) := by linarith
        rw [this]; nlinarith [sq_nonneg (P.psi1 - u)]
      linarith
    · -- (i-b): u0 = c_R
      subst hcr
      have hr0eq : r0 = P.P1 * P.cR + (1 - P.P1) * e' := by
        rw [hr0d]; apply max_eq_left
        have := mul_le_mul_of_nonneg_left (by linarith : P.cR ≤ e') hq.le; linarith
      have hcur0 : 0 ≤ (P.P1 * P.cR - P.cU) * ((P.m - P.cR) / 2) := mul_nonneg (by linarith) (by linarith)
      unfold Uf
      split_ifs with k1 k2
      · exact hcur0
      · have hu : u ≤ P.cR := by
          rw [hr0eq] at k2
          have : P.P1 * u ≤ P.P1 * P.cR := by linarith
          exact le_of_mul_le_mul_left this hp0
        have e := UI_diff P u P.cR
        have : 0 ≤ (P.cR - u) * (P.P1 * P.m + P.cU - P.P1 * (u + P.cR)) :=
          mul_nonneg (by linarith) (by linarith [mul_le_mul_of_nonneg_left hu hp0.le])
        linarith
      · push_neg at k1 k2
        have hu : P.cR < u := by
          rw [hr0eq] at k2
          have : P.P1 * P.cR < P.P1 * u := by linarith
          exact lt_of_mul_lt_mul_left this hp0.le
        -- vertex of U's diversification parabola is below c_R
        have hv : P.P1 * r0 + P.cU < 2 * (P.P1 * P.cR) := by
          rw [hr0eq, he']; nlinarith
        have e1 : (P.P1 * u - P.cU) * ((r0 - u) / (2 * (1 - P.P1))) =
            (P.P1 * u - P.cU) * (r0 - u) / (2 * (1 - P.P1)) := by ring
        rw [e1, div_le_iff₀ (by linarith)]
        have e2 : (P.P1 * P.cR - P.cU) * (r0 - P.cR) - (P.P1 * u - P.cU) * (r0 - u)
            = (u - P.cR) * (P.P1 * (u + P.cR) - P.P1 * r0 - P.cU) := by ring
        have h5 : 0 ≤ (u - P.cR) * (P.P1 * (u + P.cR) - P.P1 * r0 - P.cU) :=
          mul_nonneg (by linarith) (by linarith [mul_lt_mul_of_pos_left hu hp0])
        have h6 : r0 - P.cR ≤ (1 - P.P1) * (P.m - P.cR) := by
          rw [hr0eq, he']; linarith [mul_le_mul_of_nonneg_left hrm hq.le]
        have h7 := mul_le_mul_of_nonneg_left h6 (by linarith : (0:ℝ) ≤ P.P1 * P.cR - P.cU)
        have e3 : (P.P1 * P.cR - P.cU) * ((P.m - P.cR) / 2) * (2 * (1 - P.P1)) =
            (P.P1 * P.cR - P.cU) * ((1 - P.P1) * (P.m - P.cR)) := by ring
        rw [e3]; linarith

lemma nash_summary (P : Params) (hP : P.Standing)
    (H2 : P.P1 * (1 - P.P1) * P.m + 2 * P.cU < P.P1 * (3 - P.P1) * P.cR)
    (w : Prices) (hN : P.IsNash 1 w) :
    w.wU < w.wR ∧ P.P1 * w.wU + (1 - P.P1) * w.wE ≤ w.wR ∧ 2 * w.wE = P.m + P.cR ∧
    w.wU ≤ P.cR ∧ P.cU ≤ P.P1 * w.wU ∧
    (2 * (P.P1 * w.wU) = P.P1 * P.m + P.cU ∨
      (2 * (P.P1 * w.wU) < P.P1 * P.m + P.cU ∧ w.wR = P.P1 * w.wU + (1 - P.P1) * w.wE)) ∧
    P.payU 1 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) ∧
    P.payR 1 w = (1 - P.P1) * (P.m - P.cR) ^ 2 / 8 := by
  obtain ⟨hk, h3, hea, hac⟩ := facts P hP H2
  have h1 := notIV P hP hea h3 w hN
  have h2 := notIII P hP H2 w hN h1
  obtain ⟨C1, C2, C3⟩ := regionI P hP hac w hN h1 h2
  have hU1' : P.cU ≤ P.P1 * w.wU := by
    have := hN.1.1; rw [div_le_iff₀ hP.2.1] at this; linarith
  refine ⟨h1, h2, C1, C2, hU1', C3, ?_, ?_⟩
  · rw [payU_eq]; exact Uf_I P _ _ _ h1 h2
  · rw [payR_eq, Rf_I P _ _ _ h1 h2]
    have : w.wE = (P.m + P.cR) / 2 := by linarith
    rw [this]; ring

end CSProp2V

open CSProp2V in
theorem solution (P : Params) (hP : P.Standing) (h : P.psi2 < P.cR) :
    P.IsEquilibrium 1 ⟨P.priceI.wU, max P.priceI.wR P.cR, P.priceI.wE⟩ ∧ ∀ w, P.IsEquilibrium 1 w →
      P.Contingent 1 w ∧ w.wU = P.priceI.wU ∧ w.wE = (P.m + P.cR) / 2 ∧
      (P.psi1 ≤ P.cR → P.P1 * w.wU + P.P0 * w.wE ≤ w.wR) ∧
      (P.cR < P.psi1 → w.wR = P.P1 * w.wU + P.P0 * w.wE) := by
  have H2 := (c_psi2 P hP).mp h
  have hpsi1 := c_psi1 P hP
  have hp0 := hP.2.1
  set u0 := if P.psi1 < P.cR then P.psi1 else P.cR with hu0d
  have hpI := priceI_eq P
  rw [← hu0d] at hpI
  have hu0 : (P.psi1 < P.cR ∧ u0 = P.psi1) ∨ (¬ P.psi1 < P.cR ∧ u0 = P.cR) := by
    rw [hu0d]; split_ifs with hh
    · left; exact ⟨hh, rfl⟩
    · right; exact ⟨hh, rfl⟩
  have hN0 := w0_nash P hP H2 u0 hu0
  have hw0 : (⟨P.priceI.wU, max P.priceI.wR P.cR, P.priceI.wE⟩ : Prices) =
      ⟨u0, max (P.P1 * u0 + (1 - P.P1) * ((P.m + P.cR) / 2)) P.cR, (P.m + P.cR) / 2⟩ := by
    rw [hpI]
  rw [hw0]
  -- U's payoff at any Nash equilibrium is below that at u0, with equality only at u0
  have key : ∀ u : ℝ, u ≤ P.cR → P.cU ≤ P.P1 * u →
      (P.P1 * u - P.cU) * ((P.m - u) / 2) < (P.P1 * u0 - P.cU) * ((P.m - u0) / 2) ∨ u = u0 := by
    intro u hu1 hu2
    by_cases he : u = u0
    · right; exact he
    left
    have e := UI_diff P u u0
    rcases hu0 with ⟨hh, hu⟩ | ⟨hh, hu⟩
    · have hp1s : 2 * (P.P1 * u0) = P.P1 * P.m + P.cU := by rw [hu]; unfold Params.psi1; field_simp
      have : 0 < (u0 - u) * (P.P1 * P.m + P.cU - P.P1 * (u + u0)) := by
        have : P.P1 * P.m + P.cU - P.P1 * (u + u0) = P.P1 * (u0 - u) := by linarith
        rw [this]
        have : u0 - u ≠ 0 := fun h0 => he (by linarith)
        have := mul_pos hp0 (by positivity : 0 < (u0 - u) ^ 2)
        nlinarith
      linarith
    · have h2 := mt hpsi1.mpr hh; push_neg at h2
      have hlt : u < u0 := lt_of_le_of_ne (by rw [hu]; exact hu1) he
      have : 0 < (u0 - u) * (P.P1 * P.m + P.cU - P.P1 * (u + u0)) := by
        apply mul_pos (by linarith)
        have := mul_lt_mul_of_pos_left hlt hp0
        rw [hu] at this ⊢; linarith
      linarith
  have s0 := nash_summary P hP H2 _ hN0
  refine ⟨⟨hN0, ?_⟩, fun w hw => ?_⟩
  · rintro ⟨w', hN', hU', hR', hs⟩
    obtain ⟨-, -, -, a4, a5, -, a7, a8⟩ := nash_summary P hP H2 w' hN'
    obtain ⟨-, -, -, -, -, -, b7, b8⟩ := s0
    rcases hs with hs | hs
    · rw [a7, b7] at hs; dsimp only at hs
      rcases key w'.wU a4 a5 with hlt | heq
      · linarith
      · rw [heq] at hs; linarith
    · rw [a8, b8] at hs; linarith
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := nash_summary P hP H2 w hw.1
    obtain ⟨-, -, -, -, -, -, b7, b8⟩ := s0
    have hwu : w.wU = u0 := by
      rcases key w.wU a4 a5 with hlt | heq
      · exfalso
        apply hw.2
        refine ⟨_, hN0, ?_, ?_, Or.inl ?_⟩
        · rw [a7, b7]; simp only; linarith
        · rw [a8, b8]
        · rw [a7, b7]; simp only; linarith
      · exact heq
    refine ⟨⟨not_le.mpr a1, by rw [CSProp2V.eta1_one]; exact a2⟩, by rw [hpI]; exact hwu,
      by linarith, fun _ => by unfold Params.P0; exact a2, fun hlt => ?_⟩
    rcases hu0 with ⟨hh, _⟩ | ⟨hh, hu⟩
    · exfalso; exact absurd hh (not_lt.mpr hlt.le)
    · rcases a6 with h6 | ⟨_, h6⟩
      · exfalso
        have h7 := hlt
        unfold Params.psi1 at h7
        rw [lt_div_iff₀ (by positivity)] at h7
        rw [hwu, hu] at h6; linarith
      · unfold Params.P0; exact h6


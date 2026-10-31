-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_3_i_ii_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:01:49.372473+00:00
-- url     : https://prove2.me/submissions/b235b093-dd27-4a30-81f0-41c0793ff896

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

namespace CSProp3C

/-- Supplier U's payoff at ρ = 0 as a function of (w_U, w_R). -/
noncomputable def Uf (P : Params) (u r : ℝ) : ℝ :=
  if r ≤ u then 0
  else if P.P1 * u + (1 - P.P1) * P.m ≤ r then (P.P1 * u - P.cU) * ((P.m - u) / 2)
  else (P.P1 * u - P.cU) * ((r - u) / (2 * (1 - P.P1)))

/-- Supplier R's payoff at ρ = 0 as a function of (w_U, w_R). -/
noncomputable def Rf (P : Params) (u r : ℝ) : ℝ :=
  if r ≤ u then (r - P.cR) * ((P.m - r) / 2)
  else if P.P1 * u + (1 - P.P1) * P.m ≤ r then 0
  else (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1)))

lemma eta1_zero (P : Params) (w : Prices) : P.eta1 0 w = P.P1 * w.wU + (1 - P.P1) * P.m := by
  simp [Params.eta1, Params.PB, Params.PG, Params.P0G, Params.P0]

lemma QU_eq (P : Params) (w : Prices) : (P.order 0 w).QU =
    if w.wR ≤ w.wU then 0
    else if P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR then (P.m - w.wU) / 2
    else (w.wR - w.wU) / (2 * (1 - P.P1)) := by
  unfold Params.order
  rw [eta1_zero]
  split_ifs <;> simp [Params.orderI, Params.orderII, Params.orderIII, Params.orderIV, Params.PB,
    Params.PG, Params.P0G, Params.P0]

lemma QR_eq (P : Params) (w : Prices) : (P.order 0 w).QR =
    if w.wR ≤ w.wU then (P.m - w.wR) / 2
    else if P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR then 0
    else ((1 - P.P1) * P.m - w.wR + P.P1 * w.wU) / (2 * (1 - P.P1)) := by
  unfold Params.order
  rw [eta1_zero]
  split_ifs <;> simp [Params.orderI, Params.orderII, Params.orderIII, Params.orderIV, Params.PB,
    Params.PG, Params.P0G, Params.P0] <;> ring

lemma P0G_zero_eq (P : Params) : P.P0G 0 = 1 - P.P1 := by
  simp [Params.P0G, Params.PG, Params.P0]
lemma P1G_zero_eq (P : Params) : P.P1G 0 = P.P1 := by simp [Params.P1G, Params.PG]

lemma payU_eq (P : Params) (w : Prices) : P.payU 0 w = Uf P w.wU w.wR := by
  unfold Params.payU Uf; rw [QU_eq]; split_ifs <;> ring

lemma payR_eq (P : Params) (w : Prices) : P.payR 0 w = Rf P w.wU w.wR := by
  unfold Params.payR Rf; rw [QR_eq]
  simp only [Params.PB, mul_zero, zero_mul, add_zero]
  split_ifs <;> ring


lemma devU (P : Params) (w : Prices) (u : ℝ) : P.payU 0 ⟨u, w.wR, w.wE⟩ = Uf P u w.wR :=
  payU_eq P _
lemma devR (P : Params) (w : Prices) (r e : ℝ) : P.payR 0 ⟨w.wU, r, e⟩ = Rf P w.wU r :=
  payR_eq P _

/-- Region facts for Uf. -/
lemma Uf_IV (P : Params) (u r : ℝ) (h : r ≤ u) : Uf P u r = 0 := by unfold Uf; rw [if_pos h]
lemma Uf_I (P : Params) (u r : ℝ) (h1 : u < r) (h2 : P.P1 * u + (1 - P.P1) * P.m ≤ r) :
    Uf P u r = (P.P1 * u - P.cU) * ((P.m - u) / 2) := by
  unfold Uf; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma Uf_M (P : Params) (u r : ℝ) (h1 : u < r) (h2 : r < P.P1 * u + (1 - P.P1) * P.m) :
    Uf P u r = (P.P1 * u - P.cU) * ((r - u) / (2 * (1 - P.P1))) := by
  unfold Uf; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]
lemma Rf_IV (P : Params) (u r : ℝ) (h : r ≤ u) : Rf P u r = (r - P.cR) * ((P.m - r) / 2) := by
  unfold Rf; rw [if_pos h]
lemma Rf_I (P : Params) (u r : ℝ) (h1 : u < r) (h2 : P.P1 * u + (1 - P.P1) * P.m ≤ r) :
    Rf P u r = 0 := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_pos h2]
lemma Rf_M (P : Params) (u r : ℝ) (h1 : u < r) (h2 : r < P.P1 * u + (1 - P.P1) * P.m) :
    Rf P u r = (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u) / (2 * (1 - P.P1))) := by
  unfold Rf; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]

/-- U's payoff never exceeds the contingent/sole formula at the same price. -/
lemma Uf_le_UI (P : Params) (hP : P.Standing) (u r : ℝ) (hu : P.cU ≤ P.P1 * u) (hum : u ≤ P.m) :
    Uf P u r ≤ (P.P1 * u - P.cU) * ((P.m - u) / 2) := by
  have hq : 0 < 1 - P.P1 := by linarith [hP.2.2.1]
  unfold Uf
  split_ifs with h1 h2
  · have := mul_nonneg (by linarith : 0 ≤ P.P1 * u - P.cU) (by linarith : 0 ≤ (P.m - u) / 2)
    linarith
  · exact le_rfl
  · push_neg at h1 h2
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith

/-- Step A: no Nash equilibrium has R undercutting U. -/
lemma notIV (P : Params) (hP : P.Standing) (hk : P.cU < P.P1 * P.m)
    (h3 : (2 - P.P1) * P.cU < P.P1 * ((1 - P.P1) * P.m + P.cR))
    (w : Prices) (hN : P.IsNash 0 w) : w.wU < w.wR := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  by_contra hIV; push_neg at hIV
  have curU : P.payU 0 w = 0 := by rw [payU_eq]; exact Uf_IV P _ _ hIV
  have curR : P.payR 0 w = (w.wR - P.cR) * ((P.m - w.wR) / 2) := by rw [payR_eq]; exact Rf_IV P _ _ hIV
  by_cases ha : P.cU < P.P1 * w.wR
  · -- U undercuts R
    have hu1 : P.cU < P.P1 * ((P.cU / P.P1 + w.wR) / 2) := by
      have : P.P1 * ((P.cU / P.P1 + w.wR) / 2) = (P.cU + P.P1 * w.wR) / 2 := by
        field_simp
      rw [this]; linarith
    have hu2 : (P.cU / P.P1 + w.wR) / 2 < w.wR := by
      have : P.cU / P.P1 < w.wR := by rw [div_lt_iff₀ hp0]; linarith
      linarith
    have hdev := hUo ((P.cU / P.P1 + w.wR) / 2) ⟨by
      have : P.cU / P.P1 < w.wR := by rw [div_lt_iff₀ hp0]; linarith
      linarith, by linarith⟩
    rw [devU, curU] at hdev
    set u' := (P.cU / P.P1 + w.wR) / 2
    by_cases h2 : P.P1 * u' + (1 - P.P1) * P.m ≤ w.wR
    · rw [Uf_I P _ _ hu2 h2] at hdev
      have := mul_pos (by linarith : 0 < P.P1 * u' - P.cU) (by linarith : 0 < (P.m - u') / 2)
      linarith
    · push_neg at h2
      rw [Uf_M P _ _ hu2 h2] at hdev
      have := mul_pos (by linarith : 0 < P.P1 * u' - P.cU)
        (div_pos (by linarith : 0 < w.wR - u') (by linarith : (0:ℝ) < 2 * (1 - P.P1)))
      linarith
  · push_neg at ha
    have hmid : P.P1 * w.wR < P.P1 * ((P.m + P.cR) / 2) := by
      have := mul_nonneg hp0.le (sub_nonneg.mpr hcm)
      have : P.P1 * P.cR > 2 * P.cU - P.P1 * P.m := by linarith
      linarith
    have hmid' : w.wR < (P.m + P.cR) / 2 := lt_of_mul_lt_mul_left hmid hp0.le
    rcases hIV.lt_or_eq with hlt | heq
    · -- R raises its price within the sole-sourcing region
      set r' := min w.wU ((P.m + P.cR) / 2) with hr'
      have hr'1 : w.wR < r' := lt_min hlt hmid'
      have hr'2 : r' ≤ w.wU := min_le_left _ _
      have hr'3 : r' ≤ (P.m + P.cR) / 2 := min_le_right _ _
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_IV P _ _ hr'2] at hdev
      have : 0 < (r' - w.wR) * (P.m + P.cR - r' - w.wR) := mul_pos (by linarith) (by linarith)
      nlinarith
    · -- wR = wU = cU/P1: R moves into the mixed region at its vertex
      have hpw : P.P1 * w.wU = P.cU := by
        have h' := hU1'; rw [← heq] at h' ⊢; linarith
      set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
      set r' := (η + P.cR) / 2 with hr'
      have hwm : w.wU < P.m := by
        by_contra hc; push_neg at hc
        have : P.P1 * P.m ≤ P.P1 * w.wU := mul_le_mul_of_nonneg_left hc hp0.le
        linarith
      have hr'1 : w.wU < r' := by
        have : (2 - P.P1) * (P.P1 * w.wU) < P.P1 * ((1 - P.P1) * P.m + P.cR) := by rw [hpw]; exact h3
        have h' : P.P1 * ((2 - P.P1) * w.wU) < P.P1 * ((1 - P.P1) * P.m + P.cR) := by linarith
        have := lt_of_mul_lt_mul_left h' hp0.le
        rw [hr', hη]; linarith
      have hcη : P.cR < η := by
        have : w.wU < η := by
          rw [hη]; have := mul_lt_mul_of_pos_left hwm hq; linarith
        linarith
      have hr'2 : r' < η := by rw [hr']; linarith
      have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR, Rf_M P _ _ hr'1 (by rw [← hη]; exact hr'2)] at hdev
      have e1 : (w.wR - P.cR) * ((P.m - w.wR) / 2) =
          (w.wU - P.cR) * (η - w.wU) / (2 * (1 - P.P1)) := by
        rw [heq, hη]; field_simp; ring
      have e2 : (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) =
          (r' - P.cR) * (η - r') / (2 * (1 - P.P1)) := by rw [hη]; ring
      rw [e1, e2, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have : (r' - P.cR) * (η - r') - (w.wU - P.cR) * (η - w.wU) = (w.wU - r') ^ 2 := by
        rw [hr']; ring
      have : 0 < (w.wU - r') ^ 2 := by
        have : w.wU - r' ≠ 0 := by linarith
        positivity
      linarith

/-- U's contingent-region payoff: comparison of two prices. -/
lemma UI_diff (P : Params) (x y : ℝ) :
    (P.P1 * y - P.cU) * ((P.m - y) / 2) - (P.P1 * x - P.cU) * ((P.m - x) / 2)
      = (y - x) * (P.P1 * P.m + P.cU - P.P1 * (x + y)) / 2 := by ring

/-- Step B: Nash equilibria in which R receives no order. -/
lemma regionI (P : Params) (hP : P.Standing) (hk : P.cU < P.P1 * P.m)
    (w : Prices) (hN : P.IsNash 0 w) (h1 : w.wU < w.wR)
    (h2 : P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR) :
    P.P1 * w.wU + (1 - P.P1) * P.m ≤ P.cR ∧
    ((2 - P.P1) * P.m + P.cU < 2 * P.cR → 2 * (P.P1 * w.wU) = P.P1 * P.m + P.cU) ∧
    (2 * P.cR ≤ (2 - P.P1) * P.m + P.cU → P.P1 * w.wU + (1 - P.P1) * P.m = P.cR) ∧
    (2 * (1 - P.P1) * P.m + P.cU ≤ (2 - P.P1) * P.cR) := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  have hwRm : w.wR ≤ P.m := hR2.trans hR3
  have hwm : w.wU < P.m := lt_of_lt_of_le h1 hwRm
  have curU : P.payU 0 w = (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) := by
    rw [payU_eq]; exact Uf_I P _ _ h1 h2
  have curR : P.payR 0 w = 0 := by rw [payR_eq]; exact Rf_I P _ _ h1 h2
  have feasU : ∀ t : ℝ, w.wU ≤ t → t ≤ P.m → P.UFeasible t := by
    intro t ht1 ht2
    refine ⟨?_, ht2⟩
    rw [div_le_iff₀ hp0]; linarith [mul_le_mul_of_nonneg_left ht1 hp0.le]
  -- B1
  have B1 : P.P1 * w.wU + (1 - P.P1) * P.m ≤ P.cR := by
    by_contra hc; push_neg at hc
    set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
    have hwη : w.wU < η := by rw [hη]; linarith [mul_pos hq (sub_pos.mpr hwm)]
    have hηm : η ≤ P.m := by rw [hη]; linarith [mul_nonneg hp0.le (sub_nonneg.mpr hU2)]
    set r' := (max w.wU P.cR + η) / 2 with hr'
    have hmx1 : w.wU ≤ max w.wU P.cR := le_max_left _ _
    have hmx2 : P.cR ≤ max w.wU P.cR := le_max_right _ _
    have hmx3 : max w.wU P.cR < η := max_lt hwη hc
    have hdev := hRo r' P.m ⟨by linarith, by linarith, le_rfl⟩
    rw [devR, curR, Rf_M P _ _ (by linarith) (by rw [← hη]; linarith)] at hdev
    have : 0 < (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) :=
      mul_pos (by linarith) (div_pos (by linarith) (by linarith))
    linarith
  -- a generic upward deviation inside the contingent region
  have up : ∀ t : ℝ, w.wU < t → 2 * (P.P1 * t) ≤ P.P1 * P.m + P.cU → t < w.wR →
      P.P1 * t + (1 - P.P1) * P.m ≤ w.wR → False := by
    intro t ht1 ht2 ht3 ht4
    have hdev := hUo t (feasU t ht1.le (by linarith))
    rw [devU, curU, Uf_I P _ _ ht3 ht4] at hdev
    have e := UI_diff P w.wU t
    have : 0 < (t - w.wU) * (P.P1 * P.m + P.cU - P.P1 * (w.wU + t)) :=
      mul_pos (by linarith) (by linarith [mul_pos hp0 (sub_pos.mpr ht1)])
    linarith
  -- deviation to min(psi1, (r - q m)/P1) for a price r ≥ cR with r ≤ w_R
  have up2 : ∀ r : ℝ, P.cR ≤ r → r ≤ w.wR → P.P1 * w.wU + (1 - P.P1) * P.m < r →
      2 * (P.P1 * w.wU) < P.P1 * P.m + P.cU → False := by
    intro r hr1 hr2 hr3 hlt
    set t := min ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((r - (1 - P.P1) * P.m) / P.P1) with ht
    have ht1 : 2 * (P.P1 * t) ≤ P.P1 * P.m + P.cU := by
      have := min_le_left ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((r - (1 - P.P1) * P.m) / P.P1)
      rw [← ht, le_div_iff₀ (by positivity)] at this; linarith
    have ht2 : P.P1 * t ≤ r - (1 - P.P1) * P.m := by
      have := min_le_right ((P.P1 * P.m + P.cU) / (2 * P.P1)) ((r - (1 - P.P1) * P.m) / P.P1)
      rw [← ht, le_div_iff₀ hp0] at this; linarith
    have ht3 : w.wU < t := by
      rw [ht]; apply lt_min
      · rw [lt_div_iff₀ (by positivity)]; linarith
      · rw [lt_div_iff₀ hp0]; linarith
    apply up t ht3 ht1 _ (by linarith)
    rcases lt_or_eq_of_le (hr2.trans hwRm) with hlt' | heq'
    · have : P.P1 * t < P.P1 * w.wR := by
        linarith [mul_lt_mul_of_pos_left hlt' hq, mul_le_mul_of_nonneg_left hr2 hp0.le]
      exact lt_of_mul_lt_mul_left this hp0.le
    · have : P.P1 * t < P.P1 * P.m := by linarith
      have := lt_of_mul_lt_mul_left this hp0.le
      linarith
  have hge : 2 * (P.P1 * w.wU) < P.P1 * P.m + P.cU → P.cR ≤ P.P1 * w.wU + (1 - P.P1) * P.m := by
    intro hlt
    by_contra hc; push_neg at hc
    exact up2 P.cR le_rfl hR1 hc hlt
  have hphi12 : P.P1 * (P.P1 * P.m - P.cU) ≥ 0 := mul_nonneg hp0.le (by linarith)
  refine ⟨B1, fun hphi => ?_, fun hphi => ?_, ?_⟩
  · -- B2a: w_U = psi1
    rcases lt_trichotomy (2 * (P.P1 * w.wU)) (P.P1 * P.m + P.cU) with hlt | heq | hgt
    · exfalso; have := hge hlt; linarith
    · exact heq
    · exfalso
      set t := (P.P1 * P.m + P.cU) / (2 * P.P1) with ht
      have hpt : 2 * (P.P1 * t) = P.P1 * P.m + P.cU := by rw [ht]; field_simp
      have ht1 : t < w.wU := by
        have : P.P1 * t < P.P1 * w.wU := by linarith
        exact lt_of_mul_lt_mul_left this hp0.le
      have htm : t ≤ P.m := by
        have : P.P1 * t ≤ P.P1 * P.m := by linarith
        exact le_of_mul_le_mul_left this hp0
      have hdev := hUo t ⟨by rw [div_le_iff₀ hp0]; linarith, htm⟩
      rw [devU, curU, Uf_I P _ _ (by linarith) (by linarith)] at hdev
      have e := UI_diff P w.wU t
      have : 0 < (w.wU - t) * (P.P1 * (w.wU + t) - (P.P1 * P.m + P.cU)) :=
        mul_pos (by linarith) (by linarith)
      linarith
  · -- B2b: w_U = ℓ
    rcases lt_or_ge (2 * (P.P1 * w.wU)) (P.P1 * P.m + P.cU) with hlt | hge'
    · have := hge hlt; linarith
    · linarith
  · -- B3
    by_contra hc; push_neg at hc
    have hphi1s : 2 * P.cR < (2 - P.P1) * P.m + P.cU := by
      have h' : (2 - P.P1) * (2 * P.cR) < (2 - P.P1) * ((2 - P.P1) * P.m + P.cU) := by
        linarith
      exact lt_of_mul_lt_mul_left h' (by linarith)
    have hl : 2 * (P.P1 * w.wU) < P.P1 * P.m + P.cU := by
      by_contra hh; push_neg at hh; linarith
    have hℓ := le_antisymm B1 (hge hl)
    rcases lt_or_eq_of_le hR1 with hRgt | hReq
    · exact up2 w.wR hR1 le_rfl (by linarith) hl
    · -- R prices at cost: U moves into the mixed region at its vertex
      set v := (P.cU / P.P1 + P.cR) / 2 with hv
      have hpv : 2 * (P.P1 * v) = P.cU + P.P1 * P.cR := by rw [hv]; field_simp
      have hwc : P.P1 * w.wU < P.P1 * P.cR := by
        have := mul_lt_mul_of_pos_left h1 hp0; rw [← hReq] at this; exact this
      have hvl : w.wU < v := by
        have : P.P1 * w.wU < P.P1 * v := by linarith
        exact lt_of_mul_lt_mul_left this hp0.le
      have hvc : v < P.cR := by
        have : P.P1 * v < P.P1 * P.cR := by linarith
        exact lt_of_mul_lt_mul_left this hp0.le
      have hdev := hUo v (feasU v hvl.le (by linarith))
      rw [devU, curU, ← hReq, Uf_M P _ _ hvc (by linarith)] at hdev
      have hcw : P.cR - w.wU = (1 - P.P1) * (P.m - w.wU) := by linarith
      have e1 : (P.P1 * w.wU - P.cU) * ((P.m - w.wU) / 2) =
          (P.P1 * w.wU - P.cU) * (P.cR - w.wU) / (2 * (1 - P.P1)) := by
        rw [hcw]; field_simp
      have e2 : (P.P1 * v - P.cU) * ((P.cR - v) / (2 * (1 - P.P1))) =
          (P.P1 * v - P.cU) * (P.cR - v) / (2 * (1 - P.P1)) := by ring
      rw [e1, e2, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e3 : (P.P1 * v - P.cU) * (P.cR - v) - (P.P1 * w.wU - P.cU) * (P.cR - w.wU)
          = P.P1 * (v - w.wU) ^ 2 := by linear_combination (w.wU - v) * hpv
      have : 0 < P.P1 * (v - w.wU) ^ 2 := by
        have : v - w.wU ≠ 0 := by linarith
        positivity
      linarith

/-- Step C: Nash equilibria in the mixed (diversification) region. -/
lemma regionM (P : Params) (hP : P.Standing)
    (w : Prices) (hN : P.IsNash 0 w) (h1 : w.wU < w.wR)
    (h2 : w.wR < P.P1 * w.wU + (1 - P.P1) * P.m) :
    2 * w.wR = P.P1 * w.wU + (1 - P.P1) * P.m + P.cR ∧
    2 * (P.P1 * w.wU) = P.cU + P.P1 * w.wR ∧
    (2 - P.P1) * P.cR < 2 * (1 - P.P1) * P.m + P.cU := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  obtain ⟨⟨hU1, hU2⟩, ⟨hR1, hR2, hR3⟩, hRo, hUo⟩ := hN
  have hU1' : P.cU ≤ P.P1 * w.wU := by rw [div_le_iff₀ hp0] at hU1; linarith
  have hq : 0 < 1 - P.P1 := by linarith
  have hwRm : w.wR ≤ P.m := hR2.trans hR3
  set η := P.P1 * w.wU + (1 - P.P1) * P.m with hη
  have hηm : η ≤ P.m := by rw [hη]; linarith [mul_nonneg hp0.le (sub_nonneg.mpr hU2)]
  have curU : P.payU 0 w = (P.P1 * w.wU - P.cU) * ((w.wR - w.wU) / (2 * (1 - P.P1))) := by
    rw [payU_eq]; exact Uf_M P _ _ h1 h2
  have curR : P.payR 0 w = (w.wR - P.cR) * (((1 - P.P1) * P.m - w.wR + P.P1 * w.wU) / (2 * (1 - P.P1))) := by
    rw [payR_eq]; exact Rf_M P _ _ h1 h2
  have curR' : P.payR 0 w = (w.wR - P.cR) * (η - w.wR) / (2 * (1 - P.P1)) := by
    rw [curR, hη]; ring
  have hcη : P.cR < η := lt_of_le_of_lt hR1 h2
  -- C1: R's price is the vertex (η + cR)/2
  have C1 : 2 * w.wR = η + P.cR := by
    set r' := (η + P.cR) / 2 with hr'
    rcases le_or_gt r' w.wU with hle | hgt
    · exfalso
      have hdev := hRo w.wU P.m ⟨by linarith, by linarith, le_rfl⟩
      rw [devR, curR', Rf_IV P _ _ le_rfl] at hdev
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
      rw [devR, curR', Rf_M P _ _ hgt (by rw [← hη]; linarith)] at hdev
      have e : (r' - P.cR) * (((1 - P.P1) * P.m - r' + P.P1 * w.wU) / (2 * (1 - P.P1))) =
          (r' - P.cR) * (η - r') / (2 * (1 - P.P1)) := by rw [hη]; ring
      rw [e, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e2 : (r' - P.cR) * (η - r') - (w.wR - P.cR) * (η - w.wR) = (w.wR - r') ^ 2 := by
        rw [hr']; ring
      have : 0 < (w.wR - r') ^ 2 := by
        have : w.wR - r' ≠ 0 := by intro h0; apply hne; linarith
        positivity
      linarith
  -- C2: U's price is the vertex (cU/P1 + wR)/2
  have C2 : 2 * (P.P1 * w.wU) = P.cU + P.P1 * w.wR := by
    set v := (P.cU / P.P1 + w.wR) / 2 with hv
    have hpv : 2 * (P.P1 * v) = P.cU + P.P1 * w.wR := by rw [hv]; field_simp
    set lam := (w.wR - (1 - P.P1) * P.m) / P.P1 with hlam
    have hpl : P.P1 * lam = w.wR - (1 - P.P1) * P.m := by rw [hlam]; field_simp
    have hlw : lam < w.wU := by
      have : P.P1 * lam < P.P1 * w.wU := by linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have hpU : P.P1 * w.wU < P.P1 * w.wR := mul_lt_mul_of_pos_left h1 hp0
    set H := fun u : ℝ => (P.P1 * u - P.cU) * (w.wR - u) with hH
    have curU' : P.payU 0 w = H w.wU / (2 * (1 - P.P1)) := by rw [curU, hH]; ring
    rcases le_or_gt (P.P1 * v) (P.P1 * lam) with hle | hgt
    · exfalso
      have hdev := hUo lam ⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩
      rw [devU, curU', Uf_I P _ _ (by linarith) (by linarith)] at hdev
      have e : (P.P1 * lam - P.cU) * ((P.m - lam) / 2) = H lam / (2 * (1 - P.P1)) := by
        have : w.wR - lam = (1 - P.P1) * (P.m - lam) := by linarith
        rw [hH]; simp only; rw [this]; field_simp
      rw [e, div_le_div_iff_of_pos_right (by linarith)] at hdev
      have e2 : H lam - H w.wU = (w.wU - lam) * (P.P1 * (w.wU + lam) - 2 * (P.P1 * v)) := by
        rw [hH]; simp only; linear_combination (w.wU - lam) * hpv
      have : 0 < (w.wU - lam) * (P.P1 * (w.wU + lam) - 2 * (P.P1 * v)) := by
        apply mul_pos (by linarith)
        have := mul_lt_mul_of_pos_left hlw hp0
        linarith
      linarith
    · by_contra hne
      have hvl : lam < v := lt_of_mul_lt_mul_left hgt hp0.le
      have hvw : v < w.wR := by
        have : P.P1 * v < P.P1 * w.wR := by linarith
        exact lt_of_mul_lt_mul_left this hp0.le
      have hdev := hUo v ⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩
      rw [devU, curU', Uf_M P _ _ hvw (by linarith)] at hdev
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
  refine ⟨C1, C2, ?_⟩
  -- C3
  have e3 : (4 - P.P1) * (P.P1 * w.wU) = 2 * P.cU + P.P1 * (1 - P.P1) * P.m + P.P1 * P.cR := by
    linear_combination 2 * C2 + P.P1 * C1 + P.P1 * hη
  have hlt : P.cR - (1 - P.P1) * P.m < P.P1 * w.wU := by linarith
  have := mul_lt_mul_of_pos_left hlt (by linarith : (0:ℝ) < 4 - P.P1)
  linarith

/-! ### Thresholds and Table 3 prices -/

lemma c_psi3 (P : Params) (hP : P.Standing) :
    P.psi3 < P.cR ↔ (2 - P.P1) * P.cU < P.P1 * ((1 - P.P1) * P.m + P.cR) := by
  have hp0 := hP.2.1
  unfold Params.psi3 Params.P0
  rw [show (1 - P.P1 + 1) / P.P1 * P.cU - (1 - P.P1) * P.m < P.cR ↔
      (2 - P.P1) * P.cU / P.P1 < (1 - P.P1) * P.m + P.cR by
    constructor <;> intro h <;> [skip; skip] <;> (field_simp at h ⊢) <;> linarith]
  rw [div_lt_iff₀ hp0]; constructor <;> intro h <;> linarith

lemma c_phi2 (P : Params) (hP : P.Standing) :
    P.phi2 ≤ P.cR ↔ 2 * (1 - P.P1) * P.m + P.cU ≤ (2 - P.P1) * P.cR := by
  have hp1 := hP.2.2.1
  unfold Params.phi2 Params.P0
  rw [div_le_iff₀ (by linarith)]; constructor <;> intro h <;> linarith

lemma c_phi1 (P : Params) :
    P.phi1 < P.cR ↔ (2 - P.P1) * P.m + P.cU < 2 * P.cR := by
  unfold Params.phi1 Params.P0
  constructor <;> intro h <;> linarith

lemma pN_a (P : Params) (h : P.phi1 < P.cR) :
    P.priceN = ⟨(P.P1 * P.m + P.cU) / (2 * P.P1), P.cR, P.m⟩ := by
  unfold Params.priceN; rw [if_pos h]; rfl

lemma pN_b (P : Params) (hP : P.Standing) (h1 : P.cR ≤ P.phi1) (h2 : P.phi2 ≤ P.cR) :
    P.priceN.wU = (P.cR - (1 - P.P1) * P.m) / P.P1 ∧ P.priceN.wR = P.cR ∧ P.priceN.wE = P.m := by
  have hp0 := hP.2.1; have hp1 := hP.2.2.1
  have hpne : P.P1 ≠ 0 := hp0.ne'
  rcases h2.lt_or_eq with h | h
  · unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_pos h]
    simp only [P0G_zero_eq P, P1G_zero_eq P]
    exact ⟨by trivial, by trivial, by trivial⟩
  · unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h.ge)]
    have h5 : (P.P0 + 1) ≠ 0 := by unfold Params.P0; intro hh; linarith
    have hc : P.cR = (2 * P.P0 * P.m + P.cU) / (P.P0 + 1) := by rw [← h]; rfl
    have h4 : (3 + P.P0) ≠ 0 := by unfold Params.P0; intro hh; linarith
    refine ⟨?_, ?_, rfl⟩ <;> simp only <;> rw [hc] <;> unfold Params.P0 at h4 h5 ⊢ <;>
      field_simp <;> ring

lemma pN_c (P : Params) (hP : P.Standing) (h1 : P.cR ≤ P.phi1) (h2 : P.cR < P.phi2) :
    P.priceN = ⟨((1 - P.P1) * P.m + P.cR + 2 * P.cU / P.P1) / (3 + (1 - P.P1)),
      (2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU) / (3 + (1 - P.P1)), P.m⟩ := by
  unfold Params.priceN; rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2.le)]; rfl

lemma nondeg (P : Params) (hP : P.Standing)
    (h3 : (2 - P.P1) * P.cU < P.P1 * ((1 - P.P1) * P.m + P.cR)) : P.cU < P.P1 * P.m := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  by_contra hc; push_neg at hc
  have heq : P.cU = P.P1 * P.m := le_antisymm hcm hc
  rw [heq] at h3
  have : P.P1 * ((2 - P.P1) * P.m) < P.P1 * ((1 - P.P1) * P.m + P.cR) := by linarith
  have := lt_of_mul_lt_mul_left this hp0.le
  linarith

lemma phi2_le_phi1 (P : Params) (hP : P.Standing)
    (hc : (2 - P.P1) * P.cR < 2 * (1 - P.P1) * P.m + P.cU) : 2 * P.cR < (2 - P.P1) * P.m + P.cU := by
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP
  have := mul_nonneg hp0.le (sub_nonneg.mpr hcm)
  have h' : (2 - P.P1) * (2 * P.cR) < (2 - P.P1) * ((2 - P.P1) * P.m + P.cU) := by linarith
  exact lt_of_mul_lt_mul_left h' (by linarith)

/-- Classification of all Nash equilibria at ρ = 0 when c_R > ψ_3. -/
lemma classify (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) (w : Prices) (hN : P.IsNash 0 w) :
    w.wU = P.priceN.wU ∧
    (P.phi2 ≤ P.cR → w.wU < w.wR ∧ P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR) ∧
    (P.cR < P.phi2 → w.wU < w.wR ∧ w.wR < P.P1 * w.wU + (1 - P.P1) * P.m ∧ w.wR = P.priceN.wR) := by
  have h3 := (c_psi3 P hP).mp h
  have hk := nondeg P hP h3
  have hp0 := hP.2.1; have hp1 := hP.2.2.1
  have hpne : P.P1 ≠ 0 := hp0.ne'
  have hA := notIV P hP hk h3 w hN
  have hphi2 := c_phi2 P hP
  have hphi1 := c_phi1 P
  by_cases hI : P.P1 * w.wU + (1 - P.P1) * P.m ≤ w.wR
  · obtain ⟨B1, B2a, B2b, B3⟩ := regionI P hP hk w hN hA hI
    have hB3 : P.phi2 ≤ P.cR := hphi2.mpr B3
    refine ⟨?_, fun _ => ⟨hA, hI⟩, fun hc => absurd hB3 (not_le.mpr hc)⟩
    by_cases h1 : P.phi1 < P.cR
    · rw [pN_a P h1]; simp only
      have := B2a (hphi1.mp h1)
      field_simp; linarith
    · push_neg at h1
      rw [(pN_b P hP h1 hB3).1]
      have := B2b (by have := mt hphi1.mpr (not_lt.mpr h1); push_neg at this; exact this)
      field_simp; linarith
  · push_neg at hI
    obtain ⟨C1, C2, C3⟩ := regionM P hP w hN hA hI
    have hlt : P.cR < P.phi2 := by
      by_contra hc; push_neg at hc; have := hphi2.mp hc; linarith
    have h1 : P.cR ≤ P.phi1 := by
      have := phi2_le_phi1 P hP C3
      by_contra hc; push_neg at hc; have := hphi1.mp hc; linarith
    have e3 : (4 - P.P1) * (P.P1 * w.wU) = 2 * P.cU + P.P1 * (1 - P.P1) * P.m + P.P1 * P.cR := by
      linear_combination 2 * C2 + P.P1 * C1
    have e4 : (4 - P.P1) * w.wR = 2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU := by
      linear_combination (4 - P.P1) / 2 * C1 + e3 / 2
    have h4 : (3 + (1 - P.P1)) ≠ 0 := by intro hh; linarith
    refine ⟨?_, fun hc => absurd hc (not_le.mpr hlt), fun _ => ⟨hA, hI, ?_⟩⟩
    · rw [pN_c P hP h1 hlt]; simp only
      field_simp; linear_combination e3
    · rw [pN_c P hP h1 hlt]; simp only
      field_simp; linear_combination e4

/-- The Table 3 profile is a Nash equilibrium at ρ = 0. -/
lemma priceN_nash (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) : P.IsNash 0 P.priceN := by
  have h3 := (c_psi3 P hP).mp h
  have hk := nondeg P hP h3
  have hP' := hP
  obtain ⟨hm, hp0, hp1, hc0, hcm, hr0, hrm⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  have hpne : P.P1 ≠ 0 := hp0.ne'
  have hphi2 := c_phi2 P hP
  have hphi1 := c_phi1 P
  -- U's payoff bound: in every region U earns at most `UI` at its own price
  by_cases ha : P.phi1 < P.cR
  · -- (i-a)
    have hc := hphi1.mp ha
    rw [pN_a P ha]
    set t := (P.P1 * P.m + P.cU) / (2 * P.P1) with ht
    have hpt : 2 * (P.P1 * t) = P.P1 * P.m + P.cU := by rw [ht]; field_simp
    have htc : t < P.cR := by
      have : P.P1 * t < P.P1 * P.cR := by
        have := mul_lt_mul_of_pos_left hc hp0
        have := mul_nonneg hq.le (sub_nonneg.mpr hcm)
        linarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have hη : P.P1 * t + (1 - P.P1) * P.m ≤ P.cR := by linarith
    have htm : t ≤ P.m := by
      have : P.P1 * t ≤ P.P1 * P.m := by linarith
      exact le_of_mul_le_mul_left this hp0
    refine ⟨⟨by rw [div_le_iff₀ hp0]; linarith, htm⟩, ⟨le_rfl, hrm, le_rfl⟩, ?_, ?_⟩
    · intro r e ⟨hr1, hr2, hr3⟩
      rw [devR, payR_eq, Rf_I P _ _ htc hη]; simp only
      rw [Rf_I P _ _ (by linarith) (by linarith)]
    · intro u ⟨hu1, hu2⟩
      have hu1' : P.cU ≤ P.P1 * u := by rw [div_le_iff₀ hp0] at hu1; linarith
      rw [devU, payU_eq]; simp only
      rw [Uf_I P _ _ htc hη]
      refine (Uf_le_UI P hP u _ hu1' hu2).trans ?_
      have e := UI_diff P u t
      have : 0 ≤ (t - u) * (P.P1 * P.m + P.cU - P.P1 * (u + t)) := by
        have : P.P1 * P.m + P.cU - P.P1 * (u + t) = P.P1 * (t - u) := by linarith
        rw [this]; nlinarith [sq_nonneg (t - u)]
      linarith
  · push_neg at ha
    by_cases hb : P.phi2 ≤ P.cR
    · -- (i-b)
      obtain ⟨eU, eR, eE⟩ := pN_b P hP ha hb
      have hb' := hphi2.mp hb
      have hc' : 2 * P.cR ≤ (2 - P.P1) * P.m + P.cU := by
        by_contra hh; push_neg at hh; exact absurd (hphi1.mpr hh) (not_lt.mpr ha)
      set l := (P.cR - (1 - P.P1) * P.m) / P.P1 with hl
      have hpl : P.P1 * l = P.cR - (1 - P.P1) * P.m := by rw [hl]; field_simp
      have hcm' : P.cR < P.m := by linarith
      have hlc : l < P.cR := by
        have : P.P1 * l < P.P1 * P.cR := by linarith [mul_lt_mul_of_pos_left hcm' hq]
        exact lt_of_mul_lt_mul_left this hp0.le
      have hlU : P.cU ≤ P.P1 * l := by
        have := mul_nonneg hq.le (sub_nonneg.mpr hcm)
        nlinarith
      have hlm : l ≤ P.m := by linarith
      have hpw : P.priceN = ⟨l, P.cR, P.m⟩ := by
        rcases hpN : P.priceN with ⟨a1, a2, a3⟩
        rw [hpN] at eU eR eE; simp only at eU eR eE; rw [eU, eR, eE]
      rw [hpw]
      refine ⟨⟨by rw [div_le_iff₀ hp0]; linarith, hlm⟩, ⟨le_rfl, hrm, le_rfl⟩, ?_, ?_⟩
      · intro r e ⟨hr1, hr2, hr3⟩
        rw [devR, payR_eq]; simp only
        rw [Rf_I P _ _ hlc (by linarith), Rf_I P _ _ (by linarith) (by linarith)]
      · intro u ⟨hu1, hu2⟩
        have hu1' : P.cU ≤ P.P1 * u := by rw [div_le_iff₀ hp0] at hu1; linarith
        rw [devU, payU_eq]; simp only
        rw [Uf_I P _ _ hlc (by linarith)]
        have hcur : 0 ≤ (P.P1 * l - P.cU) * ((P.m - l) / 2) :=
          mul_nonneg (by linarith) (by linarith)
        unfold Uf
        split_ifs with g1 g2
        · exact hcur
        · -- contingent deviation: u ≤ l ≤ psi1
          have hul : P.P1 * u ≤ P.P1 * l := by linarith
          have hul' : u ≤ l := le_of_mul_le_mul_left hul hp0
          have e := UI_diff P u l
          have : 0 ≤ (l - u) * (P.P1 * P.m + P.cU - P.P1 * (u + l)) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
        · -- mixed deviation: l < u < cR, and the vertex lies below l
          push_neg at g1 g2
          have hlu : P.P1 * l < P.P1 * u := by linarith
          have hlu' : l < u := lt_of_mul_lt_mul_left hlu hp0.le
          have e1 : (P.P1 * l - P.cU) * ((P.m - l) / 2) =
              (P.P1 * l - P.cU) * (P.cR - l) / (2 * (1 - P.P1)) := by
            have : P.cR - l = (1 - P.P1) * (P.m - l) := by linarith
            rw [this]; field_simp
          have e2 : (P.P1 * u - P.cU) * ((P.cR - u) / (2 * (1 - P.P1))) =
              (P.P1 * u - P.cU) * (P.cR - u) / (2 * (1 - P.P1)) := by ring
          rw [e1, e2, div_le_div_iff_of_pos_right (by linarith)]
          have e3 : (P.P1 * l - P.cU) * (P.cR - l) - (P.P1 * u - P.cU) * (P.cR - u)
              = (u - l) * (P.P1 * (u + l) - P.P1 * P.cR - P.cU) := by ring
          have : 0 ≤ (u - l) * (P.P1 * (u + l) - P.P1 * P.cR - P.cU) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
    · -- (ii)
      push_neg at hb
      have hb' : (2 - P.P1) * P.cR < 2 * (1 - P.P1) * P.m + P.cU := by
        by_contra hh; push_neg at hh; exact absurd (hphi2.mpr hh) (not_le.mpr hb)
      rw [pN_c P hP ha hb]
      set u0 := ((1 - P.P1) * P.m + P.cR + 2 * P.cU / P.P1) / (3 + (1 - P.P1)) with hu0
      set r0 := (2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU) / (3 + (1 - P.P1)) with hr0d
      have h4 : (3 + (1 - P.P1)) ≠ 0 := by intro hh; linarith
      have eu : (4 - P.P1) * (P.P1 * u0) = P.P1 * (1 - P.P1) * P.m + P.P1 * P.cR + 2 * P.cU := by
        rw [hu0]; field_simp; ring
      have er : (4 - P.P1) * r0 = 2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU := by
        rw [hr0d]; field_simp; ring
      have h4p : (0:ℝ) < 4 - P.P1 := by linarith
      -- vertex identities
      have vR : 2 * r0 = P.P1 * u0 + (1 - P.P1) * P.m + P.cR := by
        have : (4 - P.P1) * (2 * r0) = (4 - P.P1) * (P.P1 * u0 + (1 - P.P1) * P.m + P.cR) := by
          linear_combination 2 * er - eu
        exact mul_left_cancel₀ h4p.ne' this
      have vU : 2 * (P.P1 * u0) = P.cU + P.P1 * r0 := by
        have : (4 - P.P1) * (2 * (P.P1 * u0)) = (4 - P.P1) * (P.cU + P.P1 * r0) := by
          linear_combination 2 * eu - P.P1 * er
        exact mul_left_cancel₀ h4p.ne' this
      have hur : u0 < r0 := by
        have er' : (4 - P.P1) * (P.P1 * r0) = P.P1 * (2 * (1 - P.P1) * P.m + 2 * P.cR + P.cU) := by
          linear_combination P.P1 * er
        have : (4 - P.P1) * (P.P1 * u0) < (4 - P.P1) * (P.P1 * r0) := by linarith
        have := lt_of_mul_lt_mul_left this h4p.le
        exact lt_of_mul_lt_mul_left this hp0.le
      have hrη : r0 < P.P1 * u0 + (1 - P.P1) * P.m := by
        have : (4 - P.P1) * r0 < (4 - P.P1) * (P.P1 * u0 + (1 - P.P1) * P.m) := by linarith
        exact lt_of_mul_lt_mul_left this h4p.le
      have hcr : P.cR ≤ r0 := by linarith
      have hrm0 : r0 ≤ P.m := by
        have : (4 - P.P1) * r0 ≤ (4 - P.P1) * P.m := by linarith
        exact le_of_mul_le_mul_left this h4p
      have huU : P.cU < P.P1 * u0 := by
        have : (4 - P.P1) * P.cU < (4 - P.P1) * (P.P1 * u0) := by linarith
        exact lt_of_mul_lt_mul_left this h4p.le
      refine ⟨⟨by rw [div_le_iff₀ hp0]; linarith, by linarith⟩, ⟨hcr, hrm0, le_rfl⟩, ?_, ?_⟩
      · intro r e ⟨hr1, hr2, hr3⟩
        rw [devR, payR_eq]; simp only
        rw [Rf_M P _ _ hur hrη]
        set η := P.P1 * u0 + (1 - P.P1) * P.m with hη
        have e0 : (r0 - P.cR) * (((1 - P.P1) * P.m - r0 + P.P1 * u0) / (2 * (1 - P.P1))) =
            (r0 - P.cR) * (η - r0) / (2 * (1 - P.P1)) := by rw [hη]; ring
        rw [e0]
        have hG : ∀ x, (x - P.cR) * (η - x) ≤ (r0 - P.cR) * (η - r0) := by
          intro x
          have : (r0 - P.cR) * (η - r0) - (x - P.cR) * (η - x) = (x - r0) ^ 2 := by
            linear_combination (x - r0) * vR
          have := sq_nonneg (x - r0); linarith
        have hG0 : 0 ≤ (r0 - P.cR) * (η - r0) := mul_nonneg (by linarith) (by linarith)
        unfold Rf
        split_ifs with g1 g2
        · -- sole sourcing from R
          have : (r - P.cR) * ((P.m - r) / 2) ≤ (r - P.cR) * (η - r) / (2 * (1 - P.P1)) := by
            rw [mul_div_assoc]
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            rw [div_le_div_iff₀ (by norm_num) (by linarith)]
            have := mul_le_mul_of_nonneg_left g1 hp0.le
            rw [hη]; linarith
          exact this.trans (div_le_div_of_nonneg_right (hG r) (by linarith))
        · exact div_nonneg hG0 (by linarith)
        · have e5 : (r - P.cR) * (((1 - P.P1) * P.m - r + P.P1 * u0) / (2 * (1 - P.P1))) =
              (r - P.cR) * (η - r) / (2 * (1 - P.P1)) := by rw [hη]; ring
          rw [e5]
          exact div_le_div_of_nonneg_right (hG r) (by linarith)
      · intro u ⟨hu1, hu2⟩
        have hu1' : P.cU ≤ P.P1 * u := by rw [div_le_iff₀ hp0] at hu1; linarith
        rw [devU, payU_eq]; simp only
        rw [Uf_M P _ _ hur hrη]
        have e0 : (P.P1 * u0 - P.cU) * ((r0 - u0) / (2 * (1 - P.P1))) =
            (P.P1 * u0 - P.cU) * (r0 - u0) / (2 * (1 - P.P1)) := by ring
        rw [e0]
        have hH : ∀ x, (P.P1 * x - P.cU) * (r0 - x) ≤ (P.P1 * u0 - P.cU) * (r0 - u0) := by
          intro x
          have : (P.P1 * u0 - P.cU) * (r0 - u0) - (P.P1 * x - P.cU) * (r0 - x) = P.P1 * (x - u0) ^ 2 := by
            linear_combination (x - u0) * vU
          have := mul_nonneg hp0.le (sq_nonneg (x - u0)); linarith
        have hH0 : 0 ≤ (P.P1 * u0 - P.cU) * (r0 - u0) := mul_nonneg (by linarith) (by linarith)
        unfold Uf
        split_ifs with g1 g2
        · exact div_nonneg hH0 (by linarith)
        · -- contingent deviation
          push_neg at g1
          have : (P.P1 * u - P.cU) * ((P.m - u) / 2) ≤ (P.P1 * u - P.cU) * (r0 - u) / (2 * (1 - P.P1)) := by
            rw [mul_div_assoc]
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            rw [div_le_div_iff₀ (by norm_num) (by linarith)]
            linarith
          exact this.trans (div_le_div_of_nonneg_right (hH u) (by linarith))
        · have e5 : (P.P1 * u - P.cU) * ((r0 - u) / (2 * (1 - P.P1))) =
              (P.P1 * u - P.cU) * (r0 - u) / (2 * (1 - P.P1)) := by ring
          rw [e5]
          exact div_le_div_of_nonneg_right (hH u) (by linarith)

end CSProp3C
open CSProp3C in
theorem solution (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) :
    P.IsEquilibrium 0 P.priceN ∧ ∀ w, P.IsEquilibrium 0 w →
      w.wU = P.priceN.wU ∧
      (P.phi2 ≤ P.cR → (P.order 0 w).QR = 0 ∧ 0 < (P.order 0 w).QU) ∧
      (P.cR < P.phi2 → w.wR = P.priceN.wR ∧ 0 < (P.order 0 w).QU ∧ 0 < (P.order 0 w).QR) := by
  have hp1 := hP.2.2.1
  have hq : 0 < 1 - P.P1 := by linarith
  have hE := priceN_nash P hP h
  -- payoffs of any Nash equilibrium coincide with those of the Table 3 profile
  have same : ∀ w, P.IsNash 0 w → P.payU 0 w = P.payU 0 P.priceN ∧ P.payR 0 w = P.payR 0 P.priceN := by
    intro w hw
    obtain ⟨hU, hI, hM⟩ := classify P hP h w hw
    obtain ⟨hU0, hI0, hM0⟩ := classify P hP h _ hE
    rw [payU_eq, payU_eq, payR_eq, payR_eq]
    by_cases hb : P.phi2 ≤ P.cR
    · obtain ⟨a1, a2⟩ := hI hb
      obtain ⟨b1, b2⟩ := hI0 hb
      rw [Uf_I P _ _ a1 a2, Uf_I P _ _ b1 b2, Rf_I P _ _ a1 a2, Rf_I P _ _ b1 b2, hU]
      exact ⟨rfl, rfl⟩
    · push_neg at hb
      obtain ⟨-, -, a3⟩ := hM hb
      rw [hU, a3]
      exact ⟨rfl, rfl⟩
  refine ⟨⟨hE, ?_⟩, fun w hw => ?_⟩
  · rintro ⟨w', hN', hU', hR', hs⟩
    obtain ⟨e1, e2⟩ := same w' hN'
    rcases hs with hs | hs <;> linarith
  · obtain ⟨hU, hI, hM⟩ := classify P hP h w hw.1
    have hwRm : w.wR ≤ P.m := hw.1.2.1.2.1.trans hw.1.2.1.2.2
    refine ⟨hU, fun hb => ?_, fun hb => ?_⟩
    · obtain ⟨a1, a2⟩ := hI hb
      rw [QR_eq, QU_eq, if_neg (not_le.mpr a1), if_pos a2, if_neg (not_le.mpr a1), if_pos a2]
      exact ⟨rfl, by linarith⟩
    · obtain ⟨a1, a2, a3⟩ := hM hb
      rw [QR_eq, QU_eq, if_neg (not_le.mpr a1), if_neg (not_le.mpr a2), if_neg (not_le.mpr a1),
        if_neg (not_le.mpr a2)]
      exact ⟨a3, div_pos (by linarith) (by linarith), div_pos (by linarith) (by linarith)⟩

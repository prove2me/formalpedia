-- Prove2me | solution 1 for ChannelRebate.Effort.theorem2_coordination_of_set
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:05:06.331287+00:00
-- url     : https://prove2.me/submissions/b23d0e79-c2b0-456d-acab-f16c16223472

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace CRET2

open ChannelRebate.Effort CachonCoord.Newsvendor

lemma integral_demandLaw (e : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ d, f d ∂(demandLaw e) = ∫ x in (0:ℝ)..1, f (e * x) := by
  unfold demandLaw unifLaw
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

/-- closed form of `E min(Q, eξ)` -/
lemma sales_le (Q e : ℝ) (hQ : 0 ≤ Q) (he : 0 < e) (hQe : Q ≤ e) :
    expSales (demandLaw e) Q = Q - Q ^ 2 / (2 * e) := by
  unfold expSales
  rw [integral_demandLaw e _ (by fun_prop)]
  have h0 : (0:ℝ) ≤ Q / e := div_nonneg hQ he.le
  have h1 : Q / e ≤ 1 := (div_le_one he).2 hQe
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q / e)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have e1 : ∫ x in (0:ℝ)..Q / e, min Q (e * x) = ∫ x in (0:ℝ)..Q / e, e * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    have : e * x ≤ Q := by
      have := mul_le_mul_of_nonneg_left hx.2 he.le
      rwa [mul_div_cancel₀ _ he.ne'] at this
    exact min_eq_right this
  have e2 : ∫ x in Q / e..1, min Q (e * x) = ∫ x in Q / e..(1:ℝ), Q := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    have : Q ≤ e * x := by
      have := mul_le_mul_of_nonneg_left hx.1 he.le
      rwa [mul_div_cancel₀ _ he.ne'] at this
    exact min_eq_left this
  rw [e1, e2, intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma sales_ge (Q e : ℝ) (he : 0 ≤ e) (hQe : e ≤ Q) :
    expSales (demandLaw e) Q = e / 2 := by
  unfold expSales
  rw [integral_demandLaw e _ (by fun_prop)]
  have e1 : ∫ x in (0:ℝ)..1, min Q (e * x) = ∫ x in (0:ℝ)..1, e * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    have : e * x ≤ Q := by nlinarith [hx.1, hx.2]
    exact min_eq_right this
  rw [e1, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma leftover_eq (Q e : ℝ) :
    expLeftover (demandLaw e) Q = Q - expSales (demandLaw e) Q := by
  unfold expLeftover expSales
  rw [integral_demandLaw e _ (by fun_prop), integral_demandLaw e _ (by fun_prop)]
  have : ∫ x in (0:ℝ)..1, max (Q - e * x) 0 = ∫ x in (0:ℝ)..1, (Q - min Q (e * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rcases le_total Q (e * x) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this, intervalIntegral.integral_sub intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const]
  simp

lemma reb_le (Q e T : ℝ) (hQT : Q ≤ T) : rebateUnits Q e T = 0 := by
  unfold rebateUnits rebateUnitsLaw
  rw [integral_demandLaw e _ (by fun_prop)]
  have : ∫ x in (0:ℝ)..1, max (min Q (e * x) - T) 0 = ∫ x in (0:ℝ)..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    exact max_eq_right (by linarith [min_le_left Q (e * x)])
  rw [this]; simp

lemma reb_ge (Q e T : ℝ) (hQT : T ≤ Q) :
    rebateUnits Q e T = expSales (demandLaw e) Q - expSales (demandLaw e) T := by
  unfold rebateUnits rebateUnitsLaw expSales
  rw [integral_demandLaw e _ (by fun_prop), integral_demandLaw e _ (by fun_prop),
    integral_demandLaw e _ (by fun_prop)]
  have : ∫ x in (0:ℝ)..1, max (min Q (e * x) - T) 0
      = ∫ x in (0:ℝ)..1, (min Q (e * x) - min T (e * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rcases le_total (e * x) T with h | h
    · rw [min_eq_right h, min_eq_right (h.trans hQT), max_eq_right (by linarith)]; ring
    · rw [min_eq_left h, max_eq_left (by linarith [le_min hQT h])]
  rw [this, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]

lemma sales_zero (Q : ℝ) (hQ : 0 ≤ Q) : expSales (demandLaw 0) Q = 0 := by
  rw [sales_ge Q 0 le_rfl hQ]; simp

lemma ind_intervalIntegrable (g : ℝ → ℝ) (hg : Continuous g) (x y : ℝ) :
    IntervalIntegrable (fun t => g t * (Set.Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) t)
      volume x y := by
  have : (fun t => g t * (Set.Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) t)
      = (Set.Icc (0:ℝ) 1).indicator g := by
    funext t
    by_cases h : t ∈ Set.Icc (0:ℝ) 1 <;> simp [h]
  rw [this]
  apply IntegrableOn.intervalIntegrable
  apply Integrable.integrableOn
  rw [integrable_indicator_iff measurableSet_Icc]
  exact hg.continuousOn.integrableOn_compact isCompact_Icc

lemma Phi_of_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Phi x = x := by
  unfold Phi
  have : ∫ y in (0:ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y
      = ∫ y in (0:ℝ)..x, (1:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h0] at ht
    simp only
    rw [Set.indicator_of_mem (show t ∈ Set.Icc (0:ℝ) 1 from ⟨ht.1, ht.2.trans h1⟩)]
  rw [this]; simp

lemma Phi_ge_one (x : ℝ) (h1 : 1 ≤ x) : 1 ≤ Phi x := by
  unfold Phi
  have hi := ind_intervalIntegrable (fun _ => 1) continuous_const
  simp only [one_mul] at hi
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hi 0 1) (hi 1 x)]
  have h01 := Phi_of_le 1 zero_le_one le_rfl
  unfold Phi at h01
  rw [h01]
  have : 0 ≤ ∫ y in (1:ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y := by
    apply intervalIntegral.integral_nonneg h1
    intro t _
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) t
  linarith

lemma Gam_of_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Gam x = x ^ 2 / 2 := by
  unfold Gam
  have : ∫ y in (0:ℝ)..x, y * (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y
      = ∫ y in (0:ℝ)..x, y := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le h0] at ht
    simp only
    rw [Set.indicator_of_mem (show t ∈ Set.Icc (0:ℝ) 1 from ⟨ht.1, ht.2.trans h1⟩), mul_one]
  rw [this, integral_id]; ring

lemma Phi_root (x v : ℝ) (hx : 0 < x) (hv : v < 1) (h : Phi x = v) : x = v ∧ x < 1 := by
  by_cases h1 : 1 ≤ x
  · have := Phi_ge_one x h1; linarith
  · rw [not_le] at h1
    rw [Phi_of_le x hx.le h1.le] at h
    exact ⟨h, h1⟩


/-- the newsvendor part `−wQ + P·E min(Q,X) + b·E(Q−X)⁺` -/
noncomputable def nv (P w b Q e : ℝ) : ℝ :=
  -w * Q + P * expSales (demandLaw e) Q + b * (Q - expSales (demandLaw e) Q)

lemma nv_closed_le (P w b Q e : ℝ) (hb : b < w) (hw : w < P) (he : 0 < e) (hQ : 0 ≤ Q)
    (hQe : Q ≤ e) :
    nv P w b Q e = e * ((P - b) * ((P - w) / (P - b)) ^ 2 / 2)
      - (P - b) * (Q - e * ((P - w) / (P - b))) ^ 2 / (2 * e) := by
  unfold nv
  rw [sales_le Q e hQ he hQe]
  have : P - b ≠ 0 := by linarith
  field_simp
  ring

lemma nv_closed_ge (P w b Q e : ℝ) (he : 0 ≤ e) (hQe : e ≤ Q) :
    nv P w b Q e = (P - b) * e / 2 - (w - b) * Q := by
  unfold nv
  rw [sales_ge Q e he hQe]
  ring

lemma nv_le (P w b Q e : ℝ) (hb : b < w) (hw : w < P) (he : 0 < e) (hQ : 0 ≤ Q) :
    nv P w b Q e ≤ e * ((P - b) * ((P - w) / (P - b)) ^ 2 / 2) ∧
    (nv P w b Q e = e * ((P - b) * ((P - w) / (P - b)) ^ 2 / 2) → Q = e * ((P - w) / (P - b))) := by
  have hPb : 0 < P - b := by linarith
  set q := (P - w) / (P - b) with hq
  have hq1 : q < 1 := by rw [hq, div_lt_one hPb]; linarith
  have hq0 : 0 < q := div_pos (by linarith) hPb
  rcases le_or_gt Q e with hQe | hQe
  · rw [nv_closed_le P w b Q e hb hw he hQ hQe]
    have : 0 ≤ (P - b) * (Q - e * q) ^ 2 / (2 * e) := by positivity
    refine ⟨by linarith, fun h => ?_⟩
    have h2 : (P - b) * (Q - e * q) ^ 2 / (2 * e) = 0 := by linarith
    rcases div_eq_zero_iff.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4; linarith
    · linarith
  · rw [nv_closed_ge P w b Q e he.le hQe.le]
    have hval := nv_closed_le P w b e e hb hw he he.le le_rfl
    rw [nv_closed_ge P w b e e he.le le_rfl] at hval
    have : 0 < (P - b) * (e - e * q) ^ 2 / (2 * e) := by
      have : 0 < e - e * q := by nlinarith
      positivity
    have h3 : (w - b) * e < (w - b) * Q := mul_lt_mul_of_pos_left hQe (by linarith)
    constructor <;> [skip; intro h] <;> nlinarith

lemma nv_mono (P w b T Q e : ℝ) (hb : b < w) (hw : w < P) (he : 0 < e) (hT : 0 ≤ T)
    (hTQ : T ≤ Q) (heq : e * ((P - w) / (P - b)) ≤ T) : nv P w b Q e ≤ nv P w b T e := by
  have hPb : 0 < P - b := by linarith
  set q := (P - w) / (P - b) with hq
  rcases le_or_gt Q e with hQe | hQe
  · rw [nv_closed_le P w b Q e hb hw he (hT.trans hTQ) hQe,
      nv_closed_le P w b T e hb hw he hT (hTQ.trans hQe)]
    have h1 : (T - e * q) ^ 2 ≤ (Q - e * q) ^ 2 := by nlinarith
    have : (P - b) * (T - e * q) ^ 2 / (2 * e) ≤ (P - b) * (Q - e * q) ^ 2 / (2 * e) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left h1 hPb.le
    linarith
  · rw [nv_closed_ge P w b Q e he.le hQe.le]
    rcases le_or_gt T e with hTe | hTe
    · rw [nv_closed_le P w b T e hb hw he hT hTe]
      have hval := nv_closed_le P w b e e hb hw he he.le le_rfl
      rw [nv_closed_ge P w b e e he.le le_rfl] at hval
      have h1 : (T - e * q) ^ 2 ≤ (e - e * q) ^ 2 := by nlinarith
      have : (P - b) * (T - e * q) ^ 2 / (2 * e) ≤ (P - b) * (e - e * q) ^ 2 / (2 * e) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left h1 hPb.le
      nlinarith
    · rw [nv_closed_ge P w b T e he.le hTe.le]
      nlinarith


lemma R_eq (p w u b a T Q e : ℝ) :
    R p w u b a T Q e = nv p w b Q e + u * rebateUnits Q e T - V a e := by
  unfold R nv
  rw [leftover_eq]; ring

lemma R_eq_ge (p w u b a T Q e : ℝ) (hTQ : T ≤ Q) :
    R p w u b a T Q e = nv (p + u) w b Q e - u * expSales (demandLaw e) T - V a e := by
  rw [R_eq, reb_ge Q e T hTQ]; unfold nv; ring

lemma opt (p w u b a T eb κ Q1 : ℝ) (ha : 0 < a) (hb : b < w) (hw : w < p) (hu : 0 < u)
    (hT : 0 < T) (heb : 0 < eb)
    (hQ1 : Q1 = (p + u - w) / (p + u - b)) (hTQ : T < eb * Q1)
    (hK : (p + u - b) * Q1 ^ 2 / 2 = a * eb + u * T ^ 2 / (2 * eb ^ 2))
    (hκ : R p w u b a T (eb * Q1) eb = κ)
    (hlow : ∀ Q e, 0 ≤ Q → 0 ≤ e → nv p w b Q e - V a e < κ) :
    ∀ Q e, 0 ≤ Q → 0 ≤ e → R p w u b a T Q e ≤ κ ∧
      (R p w u b a T Q e = κ → Q = eb * Q1 ∧ e = eb) := by
  have hPb : 0 < p + u - b := by linarith
  have hwP : w < p + u := by linarith
  have hQ1pos : 0 < Q1 := by rw [hQ1]; exact div_pos (by linarith) hPb
  have hQ11 : Q1 < 1 := by rw [hQ1, div_lt_one hPb]; linarith
  set K := (p + u - b) * Q1 ^ 2 / 2 with hKdef
  -- value of h at e when T < e Q1
  have hval : ∀ e, 0 < e → T ≤ e * Q1 →
      R p w u b a T (e * Q1) e = e * K - u * (T - T ^ 2 / (2 * e)) - a * e ^ 2 / 2 := by
    intro e he hle
    have hTe : T ≤ e := by nlinarith
    rw [R_eq_ge _ _ _ _ _ _ _ _ hle, sales_le T e hT.le he hTe]
    have := nv_closed_le (p + u) w b (e * Q1) e hb hwP he (by positivity) (by nlinarith)
    rw [← hQ1] at this
    rw [this]; simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_div, sub_zero, hKdef]
    unfold V; ring
  have hκ' : κ = eb * K - u * (T - T ^ 2 / (2 * eb)) - a * eb ^ 2 / 2 := by
    rw [← hκ, hval eb heb hTQ.le]
  have hlow0 := hlow 0 0 le_rfl le_rfl
  have hκpos : 0 < κ := by
    have : nv p w b 0 0 - V a 0 = 0 := by unfold nv V; simp [sales_zero 0 le_rfl]
    linarith
  -- the polynomial identity
  have poly : ∀ e, 0 < e → e * (κ - (e * K - u * (T - T ^ 2 / (2 * e)) - a * e ^ 2 / 2))
      = a / 2 * (e - eb) ^ 2 * (e - u * T ^ 2 / (a * eb ^ 2)) := by
    intro e he
    rw [hκ', hK]
    field_simp
    ring
  -- eL := T / Q1
  set eL := T / Q1 with heL
  have heLpos : 0 < eL := div_pos hT hQ1pos
  have heLQ : eL * Q1 = T := by rw [heL]; field_simp
  have hLlow : eL * K - u * (T - T ^ 2 / (2 * eL)) - a * eL ^ 2 / 2 < κ := by
    have h1 := hval eL heLpos heLQ.ge
    have h2 : R p w u b a T (eL * Q1) eL = nv p w b T eL - V a eL := by
      rw [R_eq, heLQ, reb_le T eL T le_rfl]; ring
    have := hlow T eL hT.le heLpos.le
    linarith
  have hr : u * T ^ 2 / (a * eb ^ 2) < eL := by
    have h1 := poly eL heLpos
    have h2 : 0 < eL * (κ - (eL * K - u * (T - T ^ 2 / (2 * eL)) - a * eL ^ 2 / 2)) :=
      mul_pos heLpos (by linarith)
    rw [h1] at h2
    by_contra hc
    rw [not_lt] at hc
    have : a / 2 * (eL - eb) ^ 2 * (eL - u * T ^ 2 / (a * eb ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  intro Q e hQ he
  rcases le_or_gt Q T with hQT | hQT
  · have : R p w u b a T Q e = nv p w b Q e - V a e := by
      rw [R_eq, reb_le Q e T hQT]; ring
    have := hlow Q e hQ he
    constructor
    · linarith
    · intro h; exfalso; linarith
  rcases he.eq_or_lt with he0 | hepos
  · subst he0
    have : R p w u b a T Q 0 = (b - w) * Q := by
      rw [R_eq_ge _ _ _ _ _ _ _ _ hQT.le]
      unfold nv V
      rw [sales_zero Q hQ, sales_zero T hT.le]; ring
    rw [this]
    have : (b - w) * Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hQ
    constructor
    · linarith
    · intro h; exfalso; linarith
  rcases le_or_gt (e * Q1) T with heQ | heQ
  · have hm := nv_mono (p + u) w b T Q e hb hwP hepos hT.le hQT.le (by rw [← hQ1]; exact heQ)
    have h1 := R_eq_ge p w u b a T Q e hQT.le
    have h2 : R p w u b a T T e = nv p w b T e - V a e := by
      rw [R_eq, reb_le T e T le_rfl]; ring
    have h3 := R_eq_ge p w u b a T T e le_rfl
    have := hlow T e hT.le he
    constructor
    · linarith
    · intro h; exfalso; linarith
  · have hTe : T ≤ e := by nlinarith
    have hnv := nv_le (p + u) w b Q e hb hwP hepos hQ
    rw [← hQ1, ← hKdef] at hnv
    have hV : V a e = a * e ^ 2 / 2 := rfl
    have h1 := R_eq_ge p w u b a T Q e hQT.le
    rw [sales_le T e hT.le hepos hTe] at h1
    have hgt : eL < e := by
      rw [heL, div_lt_iff₀ hQ1pos]; linarith
    have hp := poly e hepos
    have hnn : 0 ≤ a / 2 * (e - eb) ^ 2 * (e - u * T ^ 2 / (a * eb ^ 2)) :=
      mul_nonneg (by positivity) (by linarith)
    have hhe : e * K - u * (T - T ^ 2 / (2 * e)) - a * e ^ 2 / 2 ≤ κ := by
      rw [← hp] at hnn
      have := (mul_nonneg_iff_of_pos_left hepos).1 hnn
      linarith
    constructor
    · linarith [hnv.1]
    · intro h
      have hK2 : nv (p + u) w b Q e = e * K := by linarith [hnv.1]
      have hQ := hnv.2 hK2
      have hh : e * K - u * (T - T ^ 2 / (2 * e)) - a * e ^ 2 / 2 = κ := by linarith [hnv.1]
      have : a / 2 * (e - eb) ^ 2 * (e - u * T ^ 2 / (a * eb ^ 2)) = 0 := by
        rw [← hp, hh]; ring
      rcases mul_eq_zero.1 this with h4 | h4
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h5
          have hee : e = eb := by linarith
          exact ⟨by rw [hQ, hee], hee⟩
      · exfalso; linarith


lemma alg_Q1 (p c s w z : ℝ) (h5 : (p - c) ^ 5 - z ≠ 0) (h6 : (p - c) ^ 6 - (p - c) * z ≠ 0)
    (hd : p - c ≠ 0) (hD : p - s ≠ 0)
    (hden : p + (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - z)) -
      (s + (w - c) * (((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z))) ≠ 0) :
    (p + (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - z)) - w) /
      (p + (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - z)) -
      (s + (w - c) * (((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z))))
      = (p - c) / (p - s) := by
  rw [div_eq_div_iff hden hD]
  have h6' : (p - c) ^ 6 - (p - c) * z = (p - c) * ((p - c) ^ 5 - z) := by ring
  rw [h6']
  field_simp
  ring

lemma alg_K (p c s w a T : ℝ) (ha : a ≠ 0) (h5 : (p - c) ^ 5 - 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2 ≠ 0)
    (hd : p - c ≠ 0) (hD : p - s ≠ 0) :
    (p + (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2)) -
      (s + (w - c) * (((p - c) ^ 6 - (p - s) * (4 * a ^ 2 * (p - s) ^ 3 * T ^ 2)) /
        ((p - c) ^ 6 - (p - c) * (4 * a ^ 2 * (p - s) ^ 3 * T ^ 2))))) * ((p - c) / (p - s)) ^ 2 / 2
    = a * ((p - c) ^ 2 / (2 * a * (p - s))) +
      (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2)) * T ^ 2 /
        (2 * ((p - c) ^ 2 / (2 * a * (p - s))) ^ 2) := by
  have h6' : (p - c) ^ 6 - (p - c) * (4 * a ^ 2 * (p - s) ^ 3 * T ^ 2)
      = (p - c) * ((p - c) ^ 5 - 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2) := by ring
  rw [h6']
  field_simp
  ring

lemma reb_nonneg (Q e T : ℝ) : 0 ≤ rebateUnits Q e T := by
  unfold rebateUnits rebateUnitsLaw
  exact integral_nonneg (fun _ => le_max_right _ _)

/-- the no-rebate profit is bounded by `g0²/(2a)` -/
lemma low_bound (p w b a Q e : ℝ) (ha : 0 < a) (hb : b < w) (hw : w < p) (hQ : 0 ≤ Q)
    (he : 0 ≤ e) :
    nv p w b Q e - V a e ≤ ((p - b) * ((p - w) / (p - b)) ^ 2 / 2) ^ 2 / (2 * a) := by
  set g := (p - b) * ((p - w) / (p - b)) ^ 2 / 2 with hgdef
  rcases he.eq_or_lt with h0 | hpos
  · subst h0
    unfold nv V
    rw [sales_zero Q hQ]
    have : (b - w) * Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hQ
    have : 0 ≤ g ^ 2 / (2 * a) := by positivity
    nlinarith
  · have h1 := (nv_le p w b Q e hb hw hpos hQ).1
    rw [← hgdef] at h1
    have h2 : e * g - a * e ^ 2 / 2 ≤ g ^ 2 / (2 * a) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (g - a * e)]
    unfold V; linarith

lemma Pi_val (p c s a Qb E : ℝ) (ha : 0 < a) (hsc : s < c) (hcp : c < p)
    (hQbv : Qb = (p - c) / (p - s)) (hE : E = (p - c) ^ 2 / (2 * a * (p - s))) :
    nv p c s (E * Qb) E - V a E = Lam a E := by
  have hD : 0 < p - s := by linarith
  have hd : 0 < p - c := by linarith
  have hEpos : 0 < E := by rw [hE]; positivity
  have hqlt : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; linarith
  have hQb0 : 0 ≤ Qb := by rw [hQbv]; exact (div_pos (by linarith) hD).le
  have hQQ : E * Qb ≤ E := by nlinarith
  have hnv := nv_closed_le p c s (E * Qb) E hsc hcp hEpos (by positivity) hQQ
  rw [hnv, ← hQbv]
  unfold Lam V
  rw [hE, hQbv]
  field_simp
  ring

end CRET2

open ChannelRebate.Effort CachonCoord.Newsvendor CRET2 in
theorem solution
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb))
    (ε : ℝ) (hε : 0 < ε) (hεκ : ε < κ) :
    ∀ w T : ℝ, c < w → w < p →
      (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) →
      IsLlow p c s a w T (κ - ε) → IsLbar p c s a w T κ →
        (0 < uT p c s a w T ∧ s < bT p c s a w T ∧ bT p c s a w T < w ∧ 0 < T) ∧
        optimalPairs (R p w (uT p c s a w T) (bT p c s a w T) a T) =
          {(ebarOf p s a Qb * Qb, ebarOf p s a Qb)} ∧
        R p w (uT p c s a w T) (bT p c s a w T) a T
            (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = κ ∧
        M c s w (uT p c s a w T) (bT p c s a w T) T
            (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = Lam a (ebarOf p s a Qb) - κ := by
  intro w T hcw hwp hfix hLlow hLbar
  obtain ⟨T₁, T₂, hF1, hF2, h1T, hT2⟩ := hfix
  have hT0 : 0 < T := lt_of_le_of_lt hF1.1 h1T
  have hT3 : T < T3 p c s a := lt_of_lt_of_le hT2 hF2.2.1
  have hd : 0 < p - c := by linarith
  have hDd : p - c < p - s := by linarith
  have hD : 0 < p - s := by linarith
  -- Q̄₀
  have hqlt : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; exact hDd
  have hQbv := (Phi_root Qb _ hQb.1 hqlt hQb.2).1
  have hGb : Gam Qb = Qb ^ 2 / 2 := Gam_of_le Qb hQb.1.le (by rw [hQbv]; exact hqlt.le)
  have hebv : ebarOf p s a Qb = (p - c) ^ 2 / (2 * a * (p - s)) := by
    unfold ebarOf; rw [hGb, hQbv]; field_simp
  have hebpos : 0 < ebarOf p s a Qb := by rw [hebv]; positivity
  -- ζ bounds
  set z := zeta p s a T with hz
  have hzpos' : 0 < z := by rw [hz]; unfold zeta; positivity
  have hzpos : 0 ≤ z := hzpos'.le
  have hzD : z * (p - s) < (p - c) ^ 6 := by
    have e1 : z * (p - s) = (2 * a * (p - s) ^ 2 * T) ^ 2 := by rw [hz]; unfold zeta; ring
    have e2 : (p - c) ^ 6 = (2 * a * (p - s) ^ 2 * T3 p c s a) ^ 2 := by
      unfold T3; field_simp
    rw [e1, e2]
    have : 0 < 2 * a * (p - s) ^ 2 * T := by positivity
    have : 2 * a * (p - s) ^ 2 * T < 2 * a * (p - s) ^ 2 * T3 p c s a :=
      mul_lt_mul_of_pos_left hT3 (by positivity)
    nlinarith
  have h5 : z < (p - c) ^ 5 := by
    have : (p - c) ^ 6 = (p - c) ^ 5 * (p - c) := by ring
    have : z * (p - c) ≤ z * (p - s) := mul_le_mul_of_nonneg_left hDd.le hzpos
    have : z * (p - c) < (p - c) ^ 5 * (p - c) := by linarith
    exact lt_of_mul_lt_mul_right this hd.le
  have h5' : 0 < (p - c) ^ 5 - z := by linarith
  have h6eq : (p - c) ^ 6 - (p - c) * z = (p - c) * ((p - c) ^ 5 - z) := by ring
  have h6' : 0 < (p - c) ^ 6 - (p - c) * z := by rw [h6eq]; positivity
  have hnum : 0 < (p - c) ^ 6 - (p - s) * z := by rw [mul_comm]; linarith
  have hratio1 : ((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z) < 1 := by
    rw [div_lt_one h6']; nlinarith [mul_lt_mul_of_pos_right hDd hzpos']
  have hratio0 : 0 < ((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z) :=
    div_pos hnum h6'
  set u := uT p c s a w T with hu
  set b := bT p c s a w T with hb
  have hu' : u = (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - z)) := by rw [hu]; unfold uT; rw [hz]
  have hb' : b = s + (w - c) * (((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z)) := by
    rw [hb]; unfold bT; rw [hz]
  have hupos : 0 < u := by rw [hu']; exact mul_pos (by linarith) (div_pos (by positivity) h5')
  have hbs : s < b := by rw [hb']; nlinarith [mul_pos (show 0 < w - c by linarith) hratio0]
  have hbw : b < w := by
    rw [hb']
    have : (w - c) * (((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z)) < w - c := by
      have := mul_lt_mul_of_pos_left hratio1 (show 0 < w - c by linarith)
      linarith
    linarith
  refine ⟨⟨hupos, hbs, hbw, hT0⟩, ?_⟩
  -- the low branch bound
  obtain ⟨Q0, hQ0, hLv⟩ := hLlow
  have hpb : 0 < p - b := by linarith
  have hq0lt : (p - w) / (p - b) < 1 := by rw [div_lt_one hpb]; linarith
  have hQ0v := (Phi_root Q0 _ hQ0.1 hq0lt hQ0.2).1
  set g0 := (p - b) * ((p - w) / (p - b)) ^ 2 / 2 with hg0
  have hg0pos : 0 < g0 := by
    rw [hg0]; have := div_pos (show 0 < p - w by linarith) hpb; positivity
  have helv : elowOf p b a Q0 = g0 / a := by
    unfold elowOf
    rw [Gam_of_le Q0 hQ0.1.le (by rw [hQ0v]; exact hq0lt.le), hQ0v, hg0]; ring
  have hLam : g0 ^ 2 / (2 * a) ≤ κ - ε := by
    rw [hLv, R_eq, helv]
    have hel : 0 < g0 / a := div_pos hg0pos ha
    have hnvv := nv_closed_le p w b (g0 / a * Q0) (g0 / a) hbw hwp hel
      (by rw [hQ0v]; positivity) (by
        have := mul_le_mul_of_nonneg_left (show Q0 ≤ 1 by rw [hQ0v]; exact hq0lt.le) hel.le
        linarith)
    rw [hnvv, hQ0v, ← hg0]
    have := reb_nonneg (g0 / a * ((p - w) / (p - b))) (g0 / a) T
    have : 0 ≤ u * rebateUnits (g0 / a * ((p - w) / (p - b))) (g0 / a) T :=
      mul_nonneg hupos.le this
    have hVv : V a (g0 / a) = a * (g0 / a) ^ 2 / 2 := rfl
    have : g0 ^ 2 / (2 * a) = g0 / a * g0 - a * (g0 / a) ^ 2 / 2 := by field_simp; ring
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_div, sub_zero]
    linarith
  have hlow : ∀ Q e, 0 ≤ Q → 0 ≤ e → nv p w b Q e - V a e < κ := by
    intro Q e hQ he
    have := low_bound p w b a Q e ha hbw hwp hQ he
    linarith
  -- the high branch
  obtain ⟨Qb', Q1, hQb', hQ1, hLbv⟩ := hLbar
  have hQb'v := (Phi_root Qb' _ hQb'.1 hqlt hQb'.2).1
  have hQbb : Qb' = Qb := by rw [hQb'v, hQbv]
  rw [hQbb] at hLbv
  have hPb : 0 < p + u - b := by linarith
  have hq1lt : (p + u - w) / (p + u - b) < 1 := by rw [div_lt_one hPb]; linarith
  have hQ1v := (Phi_root Q1 _ hQ1.1 hq1lt hQ1.2).1
  have hQ1d : Q1 = (p - c) / (p - s) := by
    rw [hQ1v, hu', hb']
    apply alg_Q1 p c s w z h5'.ne' h6'.ne' hd.ne' hD.ne'
    rw [← hu', ← hb']; exact hPb.ne'
  have hQ1b : Q1 = Qb := by rw [hQ1d, hQbv]
  rw [hQ1b] at hLbv
  have hTQ : T < ebarOf p s a Qb * Qb := by
    have : ebarOf p s a Qb * Qb = T3 p c s a := by
      rw [hebv, hQbv]; unfold T3; field_simp
    rw [this]; exact hT3
  have hK : (p + u - b) * Qb ^ 2 / 2 = a * ebarOf p s a Qb + u * T ^ 2 / (2 * ebarOf p s a Qb ^ 2) := by
    rw [hebv, hQbv, hu', hb', hz]
    unfold zeta
    exact alg_K p c s w a T ha.ne' (by unfold zeta at hz; rw [← hz]; exact h5'.ne') hd.ne' hD.ne'
  have hopt := opt p w u b a T (ebarOf p s a Qb) κ Qb ha hbw hwp hupos hT0 hebpos
    (by rw [← hQ1b]; exact hQ1v) hTQ hK hLbv.symm hlow
  have hQbpos : 0 < Qb := hQb.1
  refine ⟨?_, hLbv.symm, ?_⟩
  · ext ⟨Q, e⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro hx
      obtain ⟨hQ, he, hmax⟩ := hx
      have h1 := hmax (ebarOf p s a Qb * Qb) (by positivity) (ebarOf p s a Qb) hebpos.le
      have h2 := (hopt Q e hQ he).1
      exact (hopt Q e hQ he).2 (le_antisymm h2 (by rw [← hLbv] at h1; exact h1))
    · rintro ⟨rfl, rfl⟩
      refine ⟨by positivity, hebpos.le, fun Q' hQ' e' he' => ?_⟩
      rw [← hLbv]
      exact (hopt Q' e' hQ' he').1
  · -- manufacturer's profit
    have hsum : M c s w u b T (ebarOf p s a Qb * Qb) (ebarOf p s a Qb)
        = nv p c s (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) - V a (ebarOf p s a Qb)
          - R p w u b a T (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) := by
      rw [R_eq]; unfold M nv; rw [leftover_eq]; ring
    rw [hsum, ← hLbv]
    have := Pi_val p c s a Qb (ebarOf p s a Qb) ha hsc hcp hQbv hebv
    linarith

-- Prove2me | solution 1 for ChannelRebate.Effort.theorem2_existence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:34:29.546549+00:00
-- url     : https://prove2.me/submissions/f1e29daf-3d57-425d-94bb-ec115de7a47c

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

namespace CRET2

open ChannelRebate.Effort CachonCoord.Newsvendor

lemma unifLaw_eq : unifLaw = demandLaw 1 := by
  unfold demandLaw
  simp only [one_mul]
  exact (Measure.map_id).symm

noncomputable def g0F (p w b : ℝ) : ℝ := (p - w) ^ 2 / (2 * (p - b))
noncomputable def g1F (p w u b : ℝ) : ℝ := (p + u - w) ^ 2 / (2 * (p + u - b))
noncomputable def tauF (p w u b : ℝ) : ℝ := 1 - √(1 - 2 * ((g1F p w u b - g0F p w b) / u))

lemma g_alg1 (p w u b : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u) :
    g1F p w u b - g0F p w b - u * ((p - w) / (p - b) - ((p - w) / (p - b)) ^ 2 / 2)
      = (p + u - b) * ((p - w) / (p - b) - (p + u - w) / (p + u - b)) ^ 2 / 2 := by
  unfold g1F g0F
  have h1 : p - b ≠ 0 := by linarith
  have h2 : p + u - b ≠ 0 := by linarith
  field_simp
  ring

lemma g_alg2 (p w u b : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u) :
    g1F p w u b - g0F p w b - u * ((p + u - w) / (p + u - b) - ((p + u - w) / (p + u - b)) ^ 2 / 2)
      = -((p - b) * ((p + u - w) / (p + u - b) - (p - w) / (p - b)) ^ 2 / 2) := by
  unfold g1F g0F
  have h1 : p - b ≠ 0 := by linarith
  have h2 : p + u - b ≠ 0 := by linarith
  field_simp
  ring

lemma Q01_lt (p w u b : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u) :
    (p - w) / (p - b) < (p + u - w) / (p + u - b) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma tau_props (p w u b : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u) :
    u * (tauF p w u b - tauF p w u b ^ 2 / 2) = g1F p w u b - g0F p w b ∧
    (p - w) / (p - b) ≤ tauF p w u b ∧ tauF p w u b < (p + u - w) / (p + u - b) ∧
    (∀ t, 0 ≤ t → t ≤ 1 →
      (tauF p w u b < t ↔ g1F p w u b - g0F p w b < u * (t - t ^ 2 / 2))) := by
  set Q0 := (p - w) / (p - b) with hQ0
  set Q1 := (p + u - w) / (p + u - b) with hQ1
  have hpb : 0 < p - b := by linarith
  have hPb : 0 < p + u - b := by linarith
  have hQ0pos : 0 < Q0 := div_pos (by linarith) hpb
  have hQ1lt : Q1 < 1 := by rw [hQ1, div_lt_one hPb]; linarith
  have hQ01 := Q01_lt p w u b hb hw hu
  rw [← hQ0, ← hQ1] at hQ01
  have a1 := g_alg1 p w u b hb hw hu
  have a2 := g_alg2 p w u b hb hw hu
  rw [← hQ0, ← hQ1] at a1 a2
  set Y := (g1F p w u b - g0F p w b) / u with hY
  have hYu : g1F p w u b - g0F p w b = u * Y := by rw [hY]; field_simp
  have hlo : Q0 - Q0 ^ 2 / 2 ≤ Y := by
    have : 0 ≤ (p + u - b) * (Q0 - Q1) ^ 2 / 2 := by positivity
    have : u * (Q0 - Q0 ^ 2 / 2) ≤ u * Y := by linarith
    exact le_of_mul_le_mul_left this hu
  have hhi : Y < Q1 - Q1 ^ 2 / 2 := by
    have : 0 < (p - b) * (Q1 - Q0) ^ 2 / 2 := by
      have : 0 < Q1 - Q0 := by linarith
      positivity
    have : u * Y < u * (Q1 - Q1 ^ 2 / 2) := by linarith
    exact lt_of_mul_lt_mul_left this hu.le
  have hY2 : 0 ≤ 1 - 2 * Y := by nlinarith
  have hsq := Real.sq_sqrt hY2
  have hsq0 := Real.sqrt_nonneg (1 - 2 * Y)
  have htau : tauF p w u b = 1 - √(1 - 2 * Y) := rfl
  -- key monotone characterization
  have key : ∀ t, 0 ≤ t → t ≤ 1 → (1 - √(1 - 2 * Y) < t ↔ Y < t - t ^ 2 / 2) := by
    intro t _ ht1
    constructor
    · intro h
      have h1 : 1 - t < √(1 - 2 * Y) := by linarith
      have := (Real.lt_sqrt (by linarith)).1 h1
      nlinarith
    · intro h
      have h1 : 1 - t < √(1 - 2 * Y) := by
        rw [Real.lt_sqrt (by linarith)]; nlinarith
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htau, hYu]; congr 1; nlinarith
  · rw [htau]
    by_contra hc
    rw [not_le] at hc
    have := (key Q0 hQ0pos.le (by linarith)).1 hc
    linarith
  · rw [htau]
    have : 1 - Q1 < √(1 - 2 * Y) := by
      rw [Real.lt_sqrt (by linarith)]; nlinarith
    linarith
  · intro t ht0 ht1
    rw [htau, key t ht0 ht1, hYu]
    exact ⟨fun h => mul_lt_mul_of_pos_left h hu, fun h => lt_of_mul_lt_mul_left h hu.le⟩

lemma rRet_eq (p w u b T Q : ℝ) :
    rRet p w u b T Q = nv p w b Q 1 + u * rebateUnits Q 1 T := by
  unfold rRet nv rebateUnits
  rw [unifLaw_eq, leftover_eq]

lemma tau_isTau (p w u b : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u) :
    IsTau p w u b (tauF p w u b) := by
  obtain ⟨h1, h2, h3, -⟩ := tau_props p w u b hb hw hu
  have hpb : 0 < p - b := by linarith
  have hPb : 0 < p + u - b := by linarith
  have hQ0pos : 0 < (p - w) / (p - b) := div_pos (by linarith) hpb
  have hQ1lt : (p + u - w) / (p + u - b) < 1 := by rw [div_lt_one hPb]; linarith
  have hQ0lt : (p - w) / (p - b) < 1 := by rw [div_lt_one hpb]; linarith
  refine ⟨(p - w) / (p - b), (p + u - w) / (p + u - b), ⟨hQ0pos, ?_⟩, ⟨by linarith, ?_⟩,
    h2, h3.le, ?_⟩
  · rw [Phi_of_le _ hQ0pos.le hQ0lt.le]
  · rw [Phi_of_le _ (by linarith) hQ1lt.le]
  · rw [rRet_eq, rRet_eq, reb_le _ _ _ h2, reb_ge _ _ _ h3.le]
    have hwP : w < p + u := by linarith
    have e1 := nv_closed_le p w b ((p - w) / (p - b)) 1 hb hw one_pos hQ0pos.le hQ0lt.le
    have e2 := nv_closed_le (p + u) w b ((p + u - w) / (p + u - b)) 1 hb hwP one_pos
      (by linarith) hQ1lt.le
    have e3 := sales_le ((p + u - w) / (p + u - b)) 1 (by linarith) one_pos hQ1lt.le
    have e4 := sales_le (tauF p w u b) 1 (by linarith) one_pos (by linarith)
    have e5 : nv (p + u) w b ((p + u - w) / (p + u - b)) 1 =
        nv p w b ((p + u - w) / (p + u - b)) 1 +
          u * expSales (demandLaw 1) ((p + u - w) / (p + u - b)) := by unfold nv; ring
    rw [e1, e4]
    have : nv p w b ((p + u - w) / (p + u - b)) 1
        = g1F p w u b - u * expSales (demandLaw 1) ((p + u - w) / (p + u - b)) := by
      rw [e2] at e5; unfold g1F
      have : p + u - b ≠ 0 := by linarith
      rw [show (p + u - w) ^ 2 / (2 * (p + u - b)) = 1 * ((p + u - b) *
        ((p + u - w) / (p + u - b)) ^ 2 / 2) - (p + u - b) *
        ((p + u - w) / (p + u - b) - 1 * ((p + u - w) / (p + u - b))) ^ 2 / (2 * 1) by
          field_simp; ring]
      linarith
    rw [this]
    have hg0 : g0F p w b = 1 * ((p - b) * ((p - w) / (p - b)) ^ 2 / 2) - (p - b) *
        ((p - w) / (p - b) - 1 * ((p - w) / (p - b))) ^ 2 / (2 * 1) := by
      unfold g0F; field_simp; ring
    rw [← hg0]
    linarith

lemma contract_facts (p c s a w T : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hT0 : 0 ≤ T) (hT3 : T ≤ T3 p c s a) :
    0 < (p - c) ^ 5 - zeta p s a T ∧ 0 < (p - c) ^ 6 - (p - c) * zeta p s a T ∧
    0 < uT p c s a w T ∧ s ≤ bT p c s a w T ∧ bT p c s a w T < w := by
  have hd : 0 < p - c := by linarith
  have hDd : p - c < p - s := by linarith
  have hD : 0 < p - s := by linarith
  set z := zeta p s a T with hz
  have hzpos : 0 ≤ z := by rw [hz]; unfold zeta; positivity
  have hzD : z * (p - s) ≤ (p - c) ^ 6 := by
    have e1 : z * (p - s) = (2 * a * (p - s) ^ 2 * T) ^ 2 := by rw [hz]; unfold zeta; ring
    have e2 : (p - c) ^ 6 = (2 * a * (p - s) ^ 2 * T3 p c s a) ^ 2 := by
      unfold T3; field_simp
    rw [e1, e2]
    have : 0 ≤ 2 * a * (p - s) ^ 2 * T := by positivity
    have : 2 * a * (p - s) ^ 2 * T ≤ 2 * a * (p - s) ^ 2 * T3 p c s a :=
      mul_le_mul_of_nonneg_left hT3 (by positivity)
    nlinarith
  have h5 : z < (p - c) ^ 5 := by
    have : (p - c) ^ 6 = (p - c) ^ 5 * (p - c) := by ring
    by_contra hc
    rw [not_lt] at hc
    have : (p - c) ^ 5 * (p - c) < (p - c) ^ 5 * (p - s) :=
      mul_lt_mul_of_pos_left hDd (by positivity)
    nlinarith
  have h5' : 0 < (p - c) ^ 5 - z := by linarith
  have h6eq : (p - c) ^ 6 - (p - c) * z = (p - c) * ((p - c) ^ 5 - z) := by ring
  have h6' : 0 < (p - c) ^ 6 - (p - c) * z := by rw [h6eq]; positivity
  have hnum : 0 ≤ (p - c) ^ 6 - (p - s) * z := by rw [mul_comm]; linarith
  have hratio1 : ((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z) ≤ 1 := by
    rw [div_le_one h6']
    nlinarith [mul_le_mul_of_nonneg_right hDd.le hzpos]
  have hratio0 : 0 ≤ ((p - c) ^ 6 - (p - s) * z) / ((p - c) ^ 6 - (p - c) * z) :=
    div_nonneg hnum h6'.le
  refine ⟨h5', h6', ?_, ?_, ?_⟩
  · unfold uT; rw [← hz]; exact mul_pos (by linarith) (div_pos (by positivity) h5')
  · unfold bT; rw [← hz]; nlinarith [mul_nonneg (show 0 ≤ w - c by linarith) hratio0]
  · unfold bT; rw [← hz]
    have := mul_le_mul_of_nonneg_left hratio1 (show 0 ≤ w - c by linarith)
    linarith

noncomputable def m1F (p c s a w T : ℝ) : ℝ :=
  g0F p w (bT p c s a w T) / a * tauF p w (uT p c s a w T) (bT p c s a w T)
noncomputable def m2F (p c s a w T : ℝ) : ℝ :=
  (p - c) ^ 2 / (2 * a * (p - s)) * tauF p w (uT p c s a w T) (bT p c s a w T)

lemma m_cont (p c s a w : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) :
    ContinuousOn (m1F p c s a w) (Set.Icc 0 (T3 p c s a)) ∧
    ContinuousOn (m2F p c s a w) (Set.Icc 0 (T3 p c s a)) := by
  have hcf := fun T (hT : T ∈ Set.Icc 0 (T3 p c s a)) =>
    contract_facts p c s a w T hcp hsc ha hcw hwp hT.1 hT.2
  have hu : ContinuousOn (fun T => uT p c s a w T) (Set.Icc 0 (T3 p c s a)) := by
    unfold uT zeta
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro T hT; have := (hcf T hT).1; unfold zeta at this; exact this.ne'
  have hb : ContinuousOn (fun T => bT p c s a w T) (Set.Icc 0 (T3 p c s a)) := by
    unfold bT zeta
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT; have := (hcf T hT).2.1; unfold zeta at this; exact this.ne'
  have hg0 : ContinuousOn (fun T => g0F p w (bT p c s a w T)) (Set.Icc 0 (T3 p c s a)) := by
    unfold g0F
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro T hT; have := (hcf T hT).2.2.2.2; have : 0 < p - bT p c s a w T := by linarith
    positivity
  have hg1 : ContinuousOn (fun T => g1F p w (uT p c s a w T) (bT p c s a w T))
      (Set.Icc 0 (T3 p c s a)) := by
    unfold g1F
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT; have := (hcf T hT).2.2.2.2; have := (hcf T hT).2.2.1
    have : 0 < p + uT p c s a w T - bT p c s a w T := by linarith
    positivity
  have htau : ContinuousOn (fun T => tauF p w (uT p c s a w T) (bT p c s a w T))
      (Set.Icc 0 (T3 p c s a)) := by
    unfold tauF
    apply ContinuousOn.sub continuousOn_const
    apply Real.continuous_sqrt.comp_continuousOn
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (hg1.sub hg0) hu
    intro T hT; exact (hcf T hT).2.2.1.ne'
  exact ⟨(hg0.div_const a).mul htau, continuousOn_const.mul htau⟩

lemma ebar_val (p c s a Qb : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hQb : IsQbar0 p c s Qb) :
    Qb = (p - c) / (p - s) ∧ ebarOf p s a Qb = (p - c) ^ 2 / (2 * a * (p - s)) := by
  have hD : 0 < p - s := by linarith
  have hqlt : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; linarith
  have hQbv := (Phi_root Qb _ hQb.1 hqlt hQb.2).1
  refine ⟨hQbv, ?_⟩
  unfold ebarOf
  rw [Gam_of_le Qb hQb.1.le (by rw [hQbv]; exact hqlt.le), hQbv]
  field_simp

lemma Q1_val (p c s a w T : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hT0 : 0 ≤ T) (hT3 : T ≤ T3 p c s a) :
    (p + uT p c s a w T - w) / (p + uT p c s a w T - bT p c s a w T) = (p - c) / (p - s) := by
  obtain ⟨h5, h6, hu, hb, hbw⟩ := contract_facts p c s a w T hcp hsc ha hcw hwp hT0 hT3
  unfold uT bT at *
  apply alg_Q1 p c s w _ h5.ne' h6.ne' (by linarith) (by linarith)
  have : 0 < p + (w - c) * ((p - c) ^ 5 / ((p - c) ^ 5 - zeta p s a T)) -
      (s + (w - c) * (((p - c) ^ 6 - (p - s) * zeta p s a T) /
        ((p - c) ^ 6 - (p - c) * zeta p s a T))) := by linarith
  exact this.ne'

lemma fixed_exist (p c s a w T Qb : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hQb : IsQbar0 p c s Qb) (hT0 : 0 < T) (hT3 : T < T3 p c s a)
    (h1 : m1F p c s a w T < T) (h2 : T < m2F p c s a w T) :
    ∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂ := by
  obtain ⟨hc1, hc2⟩ := m_cont p c s a w hcp hsc ha hcw hwp
  have hT3pos : 0 < T3 p c s a := hT0.trans hT3
  have hfacts := fun T' (h0 : 0 ≤ T') (h3 : T' ≤ T3 p c s a) =>
    contract_facts p c s a w T' hcp hsc ha hcw hwp h0 h3
  have htp := fun T' (h0 : 0 ≤ T') (h3 : T' ≤ T3 p c s a) =>
    tau_props p w (uT p c s a w T') (bT p c s a w T') (hfacts T' h0 h3).2.2.2.2 hwp
      (hfacts T' h0 h3).2.2.1
  obtain ⟨hQbv, hebv⟩ := ebar_val p c s a Qb hcp hsc ha hQb
  -- fixed point 1 on [0, T]
  have hn10 : 0 < m1F p c s a w 0 := by
    obtain ⟨-, -, -, -, hbw⟩ := hfacts 0 le_rfl hT3pos.le
    have hpb : 0 < p - bT p c s a w 0 := by linarith
    have := (htp 0 le_rfl hT3pos.le).2.1
    have hq : 0 < (p - w) / (p - bT p c s a w 0) := div_pos (by linarith) hpb
    unfold m1F g0F
    have : 0 < (p - w) ^ 2 / (2 * (p - bT p c s a w 0)) := by
      have : 0 < p - w := by linarith
      positivity
    have : 0 < tauF p w (uT p c s a w 0) (bT p c s a w 0) := by linarith
    positivity
  have hcon1 : ContinuousOn (fun T' => m1F p c s a w T' - T') (Set.Icc 0 T) :=
    (hc1.mono (Set.Icc_subset_Icc le_rfl hT3.le)).sub continuousOn_id
  obtain ⟨T₁, hT₁, hT₁eq⟩ := intermediate_value_Icc' hT0.le hcon1
    (show (0:ℝ) ∈ Set.Icc (m1F p c s a w T - T) (m1F p c s a w 0 - 0) from
      ⟨by linarith, by linarith⟩)
  simp only at hT₁eq
  have hT₁lt : T₁ < T := by
    rcases hT₁.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hT₁eq; linarith
  -- fixed point 2 on [T, T3]
  have hn2T3 : m2F p c s a w (T3 p c s a) < T3 p c s a := by
    have := (htp _ hT3pos.le le_rfl).2.2.1
    rw [Q1_val p c s a w _ hcp hsc ha hcw hwp hT3pos.le le_rfl] at this
    unfold m2F
    have e : T3 p c s a = (p - c) ^ 2 / (2 * a * (p - s)) * ((p - c) / (p - s)) := by
      unfold T3; have : p - s ≠ 0 := by linarith
      field_simp
    have hD : 0 < p - s := by linarith
    have hE : 0 < (p - c) ^ 2 / (2 * a * (p - s)) := by
      have : 0 < p - c := by linarith
      positivity
    have := mul_lt_mul_of_pos_left this hE
    linarith
  have hcon2 : ContinuousOn (fun T' => m2F p c s a w T' - T') (Set.Icc T (T3 p c s a)) :=
    (hc2.mono (Set.Icc_subset_Icc hT0.le le_rfl)).sub continuousOn_id
  obtain ⟨T₂, hT₂, hT₂eq⟩ := intermediate_value_Icc' hT3.le hcon2
    (show (0:ℝ) ∈ Set.Icc (m2F p c s a w (T3 p c s a) - T3 p c s a) (m2F p c s a w T - T) from
      ⟨by linarith, by linarith⟩)
  simp only at hT₂eq
  have hT₂gt : T < T₂ := by
    rcases hT₂.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hT₂eq; linarith
  refine ⟨T₁, T₂, ?_, ?_, hT₁lt, hT₂gt⟩
  · have h0 : 0 ≤ T₁ := hT₁.1
    have h3 : T₁ ≤ T3 p c s a := by linarith
    obtain ⟨-, -, hu, -, hbw⟩ := hfacts T₁ h0 h3
    have hpb : 0 < p - bT p c s a w T₁ := by linarith
    have hq0 : 0 < (p - w) / (p - bT p c s a w T₁) := div_pos (by linarith) hpb
    have hq1 : (p - w) / (p - bT p c s a w T₁) < 1 := by rw [div_lt_one hpb]; linarith
    refine ⟨h0, h3, (p - w) / (p - bT p c s a w T₁), _, ⟨hq0, Phi_of_le _ hq0.le hq1.le⟩,
      tau_isTau _ _ _ _ hbw hwp hu, ?_⟩
    have e : elowOf p (bT p c s a w T₁) a ((p - w) / (p - bT p c s a w T₁)) *
        tauF p w (uT p c s a w T₁) (bT p c s a w T₁) = m1F p c s a w T₁ := by
      unfold elowOf
      rw [Gam_of_le _ hq0.le hq1.le]
      unfold m1F g0F
      field_simp
    linarith
  · have h0 : 0 ≤ T₂ := by linarith
    have h3 : T₂ ≤ T3 p c s a := hT₂.2
    obtain ⟨-, -, hu, -, hbw⟩ := hfacts T₂ h0 h3
    refine ⟨h0, h3, Qb, _, hQb, tau_isTau _ _ _ _ hbw hwp hu, ?_⟩
    rw [hebv]
    have : m2F p c s a w T₂ = (p - c) ^ 2 / (2 * a * (p - s)) *
        tauF p w (uT p c s a w T₂) (bT p c s a w T₂) := rfl
    linarith

lemma high_val (p w u b a T eb Q1 : ℝ) (hb : b < w) (hw : w < p) (hu : 0 < u)
    (hT : 0 < T) (heb : 0 < eb) (hQ1 : Q1 = (p + u - w) / (p + u - b)) (hle : T ≤ eb * Q1) :
    R p w u b a T (eb * Q1) eb = eb * ((p + u - b) * Q1 ^ 2 / 2) - u * (T - T ^ 2 / (2 * eb))
      - a * eb ^ 2 / 2 := by
  have hPb : 0 < p + u - b := by linarith
  have hwP : w < p + u := by linarith
  have hQ1pos : 0 < Q1 := by rw [hQ1]; exact div_pos (by linarith) hPb
  have hQ11 : Q1 < 1 := by rw [hQ1, div_lt_one hPb]; linarith
  have hTe : T ≤ eb := by nlinarith
  rw [R_eq_ge _ _ _ _ _ _ _ _ hle, sales_le T eb hT.le heb hTe]
  have := nv_closed_le (p + u) w b (eb * Q1) eb hb hwP heb (by positivity) (by nlinarith)
  rw [← hQ1] at this
  rw [this]; simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, sub_zero]
  unfold V; ring

lemma curve_point (p c s a Qb w T : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hQb : IsQbar0 p c s Qb) (hT0 : 0 < T) (hT3 : T < T3 p c s a) :
    (p + uT p c s a w T - w) / (p + uT p c s a w T - bT p c s a w T) = Qb ∧
    (p + uT p c s a w T - bT p c s a w T) * Qb ^ 2 / 2
      = a * ebarOf p s a Qb + uT p c s a w T * T ^ 2 / (2 * ebarOf p s a Qb ^ 2) ∧
    T < ebarOf p s a Qb * Qb ∧
    R p w (uT p c s a w T) (bT p c s a w T) a T (ebarOf p s a Qb * Qb) (ebarOf p s a Qb)
      = a * ebarOf p s a Qb ^ 2 / 2 + uT p c s a w T * T ^ 2 / ebarOf p s a Qb
        - uT p c s a w T * T := by
  obtain ⟨hQbv, hebv⟩ := ebar_val p c s a Qb hcp hsc ha hQb
  obtain ⟨h5, h6, hu, hsb, hbw⟩ := contract_facts p c s a w T hcp hsc ha hcw hwp hT0.le hT3.le
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hQ1 : (p + uT p c s a w T - w) / (p + uT p c s a w T - bT p c s a w T) = Qb := by
    rw [Q1_val p c s a w T hcp hsc ha hcw hwp hT0.le hT3.le, hQbv]
  have hK : (p + uT p c s a w T - bT p c s a w T) * Qb ^ 2 / 2
      = a * ebarOf p s a Qb + uT p c s a w T * T ^ 2 / (2 * ebarOf p s a Qb ^ 2) := by
    rw [hebv, hQbv]
    unfold uT bT zeta
    exact alg_K p c s w a T ha.ne' (by unfold zeta at h5; exact h5.ne') hd.ne' hD.ne'
  have hebpos : 0 < ebarOf p s a Qb := by rw [hebv]; positivity
  have hTQ : T < ebarOf p s a Qb * Qb := by
    have : ebarOf p s a Qb * Qb = T3 p c s a := by
      rw [hebv, hQbv]; unfold T3; field_simp
    rw [this]; exact hT3
  refine ⟨hQ1, hK, hTQ, ?_⟩
  rw [high_val p w _ _ a T _ Qb hbw hwp hu hT0 hebpos hQ1.symm hTQ.le, hK]
  field_simp
  ring

lemma quad_le (g e a : ℝ) (ha : 0 < a) : e * g - a * e ^ 2 / 2 ≤ g ^ 2 / (2 * a) := by
  rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (g - a * e)]

lemma sigma_mono (x y : ℝ) (h0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    x - x ^ 2 / 2 ≤ y - y ^ 2 / 2 := by nlinarith

lemma point_ok (p c s a Qb w T κ L : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hQb : IsQbar0 p c s Qb) (hT0 : 0 < T) (hT3 : T < T3 p c s a)
    (hκ : a * ebarOf p s a Qb ^ 2 / 2 + uT p c s a w T * T ^ 2 / ebarOf p s a Qb
        - uT p c s a w T * T = κ)
    (hL : g0F p w (bT p c s a w T) ^ 2 / (2 * a) = L) (hLκ : L < κ)
    (hm : m1F p c s a w T < T) :
    IsLlow p c s a w T L ∧ IsLbar p c s a w T κ ∧
      ∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂ := by
  obtain ⟨hQ1, hK, hTQ, hRv⟩ := curve_point p c s a Qb w T hcp hsc ha hcw hwp hQb hT0 hT3
  obtain ⟨hQbv, hebv⟩ := ebar_val p c s a Qb hcp hsc ha hQb
  obtain ⟨h5, h6, hu, hsb, hbw⟩ := contract_facts p c s a w T hcp hsc ha hcw hwp hT0.le hT3.le
  have hQb1 : Qb ≤ 1 := by rw [hQbv, div_le_one (by linarith)]; linarith
  set u := uT p c s a w T with hudef
  set b := bT p c s a w T with hbdef
  set eb := ebarOf p s a Qb with hebdef
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hebpos : 0 < eb := by rw [hebv]; positivity
  have hpb : 0 < p - b := by linarith
  have hq0 : 0 < (p - w) / (p - b) := div_pos (by linarith) hpb
  have hq1 : (p - w) / (p - b) < 1 := by rw [div_lt_one hpb]; linarith
  obtain ⟨htau1, htau2, htau3, htau4⟩ := tau_props p w u b hbw hwp hu
  set g0 := g0F p w b with hg0
  have hg0pos : 0 < g0 := by
    rw [hg0]; unfold g0F; have : 0 < p - w := by linarith
    positivity
  have hg0' : (p - b) * ((p - w) / (p - b)) ^ 2 / 2 = g0 := by
    rw [hg0]; unfold g0F; field_simp
  have hel : elowOf p b a ((p - w) / (p - b)) = g0 / a := by
    unfold elowOf; rw [Gam_of_le _ hq0.le hq1.le, ← hg0']; ring
  refine ⟨?_, ?_, ?_⟩
  · -- IsLlow
    refine ⟨(p - w) / (p - b), ⟨hq0, Phi_of_le _ hq0.le hq1.le⟩, ?_⟩
    rw [hel]
    have hela : 0 < g0 / a := div_pos hg0pos ha
    have hQ2 : g0 / a * ((p - w) / (p - b)) ≤ T := by
      have : g0 / a * ((p - w) / (p - b)) ≤ g0 / a * tauF p w u b :=
        mul_le_mul_of_nonneg_left htau2 hela.le
      have hm' : m1F p c s a w T = g0 / a * tauF p w u b := rfl
      linarith
    rw [R_eq, reb_le _ _ _ hQ2]
    rw [nv_closed_le p w b _ _ hbw hwp hela (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hq1.le hela.le])]
    rw [hg0']
    unfold V
    rw [← hL]
    field_simp
    ring
  · -- IsLbar
    refine ⟨Qb, Qb, hQb, ⟨hQb.1, ?_⟩, ?_⟩
    · rw [Phi_of_le _ hQb.1.le (by rw [hQbv, div_le_one hD]; linarith)]
      exact hQ1.symm
    · rw [hRv, hκ]
  · -- fixed points
    apply fixed_exist p c s a w T Qb hcp hsc ha hcw hwp hQb hT0 hT3 hm
    -- T < m2F: τ > T / eb
    have hm2 : m2F p c s a w T = eb * tauF p w u b := by
      rw [hebv]; rfl
    rw [hm2]
    have hθ1 : T / eb < 1 := by
      rw [div_lt_one hebpos]
      have : eb * Qb ≤ eb := mul_le_of_le_one_right hebpos.le hQb1
      linarith
    have hθ0 : 0 < T / eb := div_pos hT0 hebpos
    by_contra hc
    rw [not_lt] at hc
    have htle : tauF p w u b ≤ T / eb := by
      rw [le_div_iff₀ hebpos]; linarith
    have htau0 : 0 ≤ tauF p w u b := le_trans hq0.le htau2
    -- σ monotone
    have hσ : tauF p w u b - tauF p w u b ^ 2 / 2 ≤ T / eb - (T / eb) ^ 2 / 2 :=
      sigma_mono _ _ htau0 htle hθ1.le
    have h1 : g1F p w u b - g0 ≤ u * (T / eb - (T / eb) ^ 2 / 2) := by
      rw [← htau1]; exact mul_le_mul_of_nonneg_left hσ hu.le
    -- but κ = eb g1 - u(T - T²/(2eb)) - a eb²/2, and eb g0 - a eb²/2 ≤ g0²/(2a) = L < κ
    have hg1 : g1F p w u b = (p + u - b) * Qb ^ 2 / 2 := by
      unfold g1F; rw [← hQ1]
      have : p + u - b ≠ 0 := by linarith
      field_simp
    have hκ2 : κ = eb * g1F p w u b - u * (T - T ^ 2 / (2 * eb)) - a * eb ^ 2 / 2 := by
      rw [← hκ, hg1, hK]; field_simp; ring
    have h2 : eb * g0 - a * eb ^ 2 / 2 ≤ g0 ^ 2 / (2 * a) := quad_le g0 eb a ha
    have h3 : eb * (g1F p w u b - g0) ≤ eb * (u * (T / eb - (T / eb) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left h1 hebpos.le
    have h4 : eb * (u * (T / eb - (T / eb) ^ 2 / 2)) = u * (T - T ^ 2 / (2 * eb)) := by
      field_simp
    rw [hL] at h2
    linarith

lemma cubic_id (a eb u T κ K e : ℝ) (ha : 0 < a) (heb : 0 < eb) (he : 0 < e)
    (hK : K = a * eb + u * T ^ 2 / (2 * eb ^ 2))
    (hκ : κ = eb * K - u * (T - T ^ 2 / (2 * eb)) - a * eb ^ 2 / 2) :
    e * (κ - (e * K - u * (T - T ^ 2 / (2 * e)) - a * e ^ 2 / 2))
      = a / 2 * (e - eb) ^ 2 * (e - u * T ^ 2 / (a * eb ^ 2)) := by
  rw [hκ, hK]
  field_simp
  ring

lemma crossing (p c s a Qb w T κ : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hcw : c < w) (hwp : w < p) (hQb : IsQbar0 p c s Qb) (hT0 : 0 < T) (hT3 : T < T3 p c s a)
    (hκ : a * ebarOf p s a Qb ^ 2 / 2 + uT p c s a w T * T ^ 2 / ebarOf p s a Qb
        - uT p c s a w T * T = κ)
    (hF : g0F p w (bT p c s a w T) ^ 2 / (2 * a) = κ)
    (hκPi : κ < a * ebarOf p s a Qb ^ 2 / 2) :
    m1F p c s a w T < T := by
  obtain ⟨hQ1, hK, hTQ, -⟩ := curve_point p c s a Qb w T hcp hsc ha hcw hwp hQb hT0 hT3
  obtain ⟨hQbv, hebv⟩ := ebar_val p c s a Qb hcp hsc ha hQb
  obtain ⟨-, -, hu, -, hbw⟩ := contract_facts p c s a w T hcp hsc ha hcw hwp hT0.le hT3.le
  have hD : 0 < p - s := by linarith
  have hd : 0 < p - c := by linarith
  have hebpos : 0 < ebarOf p s a Qb := by rw [hebv]; positivity
  show g0F p w (bT p c s a w T) / a * tauF p w (uT p c s a w T) (bT p c s a w T) < T
  generalize uT p c s a w T = u at *
  generalize bT p c s a w T = b at *
  generalize ebarOf p s a Qb = eb at *
  obtain ⟨htau1, htau2, htau3, htau4⟩ := tau_props p w u b hbw hwp hu
  have hpb : 0 < p - b := by linarith
  have hPb : 0 < p + u - b := by linarith
  rw [hQ1] at htau3
  have hQb1 : Qb < 1 := by rw [hQbv, div_lt_one hD]; linarith
  have hq0 : 0 < (p - w) / (p - b) := div_pos (by linarith) hpb
  have hg0pos : 0 < g0F p w b := by
    unfold g0F; have : 0 < p - w := by linarith
    positivity
  have hg0Q : g0F p w b = (p - b) * ((p - w) / (p - b)) ^ 2 / 2 := by
    unfold g0F; field_simp
  have hg1 : g1F p w u b = (p + u - b) * Qb ^ 2 / 2 := by
    unfold g1F; rw [← hQ1]; field_simp
  -- g1 < g0 + u/2
  have hg1lt : g1F p w u b - g0F p w b < u / 2 := by
    have a2 := g_alg2 p w u b hbw hwp hu
    rw [hQ1] at a2
    have hQ01 := Q01_lt p w u b hbw hwp hu
    rw [hQ1] at hQ01
    have : 0 < (p - b) * (Qb - (p - w) / (p - b)) ^ 2 / 2 := by
      have : 0 < Qb - (p - w) / (p - b) := by linarith
      positivity
    have : Qb - Qb ^ 2 / 2 ≤ 1 / 2 := by nlinarith
    nlinarith
  set g0 := g0F p w b with hg0d
  set g1 := g1F p w u b with hg1d
  set K := (p + u - b) * Qb ^ 2 / 2 with hKd
  have hκ2 : κ = eb * K - u * (T - T ^ 2 / (2 * eb)) - a * eb ^ 2 / 2 := by
    rw [← hκ, hK]; field_simp; ring
  have hcub := fun e (he : 0 < e) => cubic_id a eb u T κ K e ha hebpos he hK hκ2
  set el := g0 / a with heldef
  have helpos : 0 < el := div_pos hg0pos ha
  have hFel : el * g0 - a * el ^ 2 / 2 = κ := by
    rw [← hF, heldef]; field_simp; ring
  -- r < T
  have hTeb : T < eb := lt_of_lt_of_le hTQ (mul_le_of_le_one_right hebpos.le hQb1.le)
  have hr : u * T ^ 2 / (a * eb ^ 2) < T := by
    have h1 : T * K - u * (T - T ^ 2 / (2 * T)) - a * T ^ 2 / 2 < κ := by
      have e1 : T * K - u * (T - T ^ 2 / (2 * T)) - a * T ^ 2 / 2
          = T * (g1 - u / 2) - a * T ^ 2 / 2 := by
        rw [hg1]; field_simp; ring
      rw [e1]
      have : T * (g1 - u / 2) < T * g0 := mul_lt_mul_of_pos_left (by linarith) hT0
      have := quad_le g0 T a ha
      rw [hF] at this
      linarith
    have h2 := hcub T hT0
    have h3 : 0 < T * (κ - (T * K - u * (T - T ^ 2 / (2 * T)) - a * T ^ 2 / 2)) :=
      mul_pos hT0 (by linarith)
    rw [h2] at h3
    by_contra hc; rw [not_lt] at hc
    have : a / 2 * (T - eb) ^ 2 * (T - u * T ^ 2 / (a * eb ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hτ1 : tauF p w u b < 1 := by linarith
  rcases le_or_gt el T with hle | hgt
  · calc el * tauF p w u b < el * 1 := mul_lt_mul_of_pos_left hτ1 helpos
      _ = el := mul_one el
      _ ≤ T := hle
  · have hne : el ≠ eb := by
      intro h
      have hg0el : g0 = a * el := by rw [heldef]; field_simp
      have : κ = a * el ^ 2 / 2 := by rw [← hFel, hg0el]; ring
      rw [h] at this
      linarith
    have hc := hcub el helpos
    have hpos : 0 < a / 2 * (el - eb) ^ 2 * (el - u * T ^ 2 / (a * eb ^ 2)) := by
      have : 0 < (el - eb) ^ 2 := by
        have : el - eb ≠ 0 := sub_ne_zero.2 hne
        positivity
      have : 0 < el - u * T ^ 2 / (a * eb ^ 2) := by linarith
      positivity
    rw [← hc] at hpos
    have hhl : el * K - u * (T - T ^ 2 / (2 * el)) - a * el ^ 2 / 2 < κ := by
      have := (mul_pos_iff_of_pos_left helpos).1 hpos
      linarith
    -- τ < T / el
    have ht0 : 0 ≤ T / el := (div_pos hT0 helpos).le
    have ht1 : T / el ≤ 1 := (div_le_one helpos).2 hgt.le
    have key : g1 - g0 < u * (T / el - (T / el) ^ 2 / 2) := by
      have e2 : el * (u * (T / el - (T / el) ^ 2 / 2)) = u * (T - T ^ 2 / (2 * el)) := by
        field_simp
      have : el * (g1 - g0) < el * (u * (T / el - (T / el) ^ 2 / 2)) := by
        rw [e2]
        have : el * K = el * g1 := by rw [hg1]
        linarith
      exact lt_of_mul_lt_mul_left this helpos.le
    have := (htau4 (T / el) ht0 ht1).2 key
    have := mul_lt_mul_of_pos_left this helpos
    rw [mul_div_cancel₀ _ helpos.ne'] at this
    exact this

lemma ratio_facts (p c s a T : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hT0 : 0 ≤ T) (hT3 : T ≤ T3 p c s a) :
    0 < (p - c) ^ 5 - zeta p s a T ∧ 0 < (p - c) ^ 6 - (p - c) * zeta p s a T ∧
    0 ≤ ((p - c) ^ 6 - (p - s) * zeta p s a T) / ((p - c) ^ 6 - (p - c) * zeta p s a T) ∧
    ((p - c) ^ 6 - (p - s) * zeta p s a T) / ((p - c) ^ 6 - (p - c) * zeta p s a T) ≤ 1 := by
  have hd : 0 < p - c := by linarith
  have hDd : p - c < p - s := by linarith
  have hD : 0 < p - s := by linarith
  set z := zeta p s a T with hz
  have hzpos : 0 ≤ z := by rw [hz]; unfold zeta; positivity
  have hzD : z * (p - s) ≤ (p - c) ^ 6 := by
    have e1 : z * (p - s) = (2 * a * (p - s) ^ 2 * T) ^ 2 := by rw [hz]; unfold zeta; ring
    have e2 : (p - c) ^ 6 = (2 * a * (p - s) ^ 2 * T3 p c s a) ^ 2 := by
      unfold T3; field_simp
    rw [e1, e2]
    have : 0 ≤ 2 * a * (p - s) ^ 2 * T := by positivity
    have : 2 * a * (p - s) ^ 2 * T ≤ 2 * a * (p - s) ^ 2 * T3 p c s a :=
      mul_le_mul_of_nonneg_left hT3 (by positivity)
    nlinarith
  have h5 : z < (p - c) ^ 5 := by
    have : (p - c) ^ 6 = (p - c) ^ 5 * (p - c) := by ring
    by_contra hc
    rw [not_lt] at hc
    have : (p - c) ^ 5 * (p - c) < (p - c) ^ 5 * (p - s) :=
      mul_lt_mul_of_pos_left hDd (by positivity)
    nlinarith
  have h6eq : (p - c) ^ 6 - (p - c) * z = (p - c) * ((p - c) ^ 5 - z) := by ring
  have h6' : 0 < (p - c) ^ 6 - (p - c) * z := by rw [h6eq]; nlinarith
  refine ⟨by linarith, h6', div_nonneg (by rw [mul_comm]; linarith) h6'.le, ?_⟩
  rw [div_le_one h6']
  nlinarith [mul_le_mul_of_nonneg_right hDd.le hzpos]

lemma curve_cont (p c s a : ℝ) (W : ℝ → ℝ) (S : Set ℝ) (hcp : c < p) (hsc : s < c)
    (ha : 0 < a) (hW : ContinuousOn W S)
    (hS : ∀ T ∈ S, c ≤ W T ∧ W T ≤ p ∧ 0 ≤ T ∧ T ≤ T3 p c s a) :
    ContinuousOn (fun T => g0F p (W T) (bT p c s a (W T) T)) S := by
  have hr := fun T (hT : T ∈ S) => ratio_facts p c s a T hcp hsc ha (hS T hT).2.2.1
    (hS T hT).2.2.2
  have hb : ContinuousOn (fun T => bT p c s a (W T) T) S := by
    unfold bT zeta
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.mul (hW.sub continuousOn_const)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT; have := (hr T hT).2.1; unfold zeta at this; exact this.ne'
  unfold g0F
  apply ContinuousOn.div ((continuousOn_const.sub hW).pow 2) (by fun_prop)
  intro T hT
  obtain ⟨-, -, h0, h1⟩ := hr T hT
  obtain ⟨hcW, hWp, -, -⟩ := hS T hT
  have : bT p c s a (W T) T ≤ s + (W T - c) := by
    unfold bT
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ W T - c by linarith)
    linarith
  have : 0 < p - bT p c s a (W T) T := by linarith
  positivity

lemma curve_cont_m1 (p c s a : ℝ) (W : ℝ → ℝ) (S : Set ℝ) (hcp : c < p) (hsc : s < c)
    (ha : 0 < a) (hW : ContinuousOn W S)
    (hS : ∀ T ∈ S, c < W T ∧ W T < p ∧ 0 ≤ T ∧ T ≤ T3 p c s a) :
    ContinuousOn (fun T => m1F p c s a (W T) T) S := by
  have hcf := fun T (hT : T ∈ S) =>
    contract_facts p c s a (W T) T hcp hsc ha (hS T hT).1 (hS T hT).2.1 (hS T hT).2.2.1
      (hS T hT).2.2.2
  have hu : ContinuousOn (fun T => uT p c s a (W T) T) S := by
    unfold uT zeta
    apply ContinuousOn.mul (hW.sub continuousOn_const)
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro T hT; have := (hcf T hT).1; unfold zeta at this; exact this.ne'
  have hb : ContinuousOn (fun T => bT p c s a (W T) T) S := by
    unfold bT zeta
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.mul (hW.sub continuousOn_const)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT; have := (hcf T hT).2.1; unfold zeta at this; exact this.ne'
  have hg0 : ContinuousOn (fun T => g0F p (W T) (bT p c s a (W T) T)) S := by
    unfold g0F
    apply ContinuousOn.div ((continuousOn_const.sub hW).pow 2) (by fun_prop)
    intro T hT; have := (hcf T hT).2.2.2.2; have := (hS T hT).2.1
    have : 0 < p - bT p c s a (W T) T := by linarith
    positivity
  have hg1 : ContinuousOn (fun T => g1F p (W T) (uT p c s a (W T) T) (bT p c s a (W T) T)) S := by
    unfold g1F
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT; have := (hcf T hT).2.2.2.2; have := (hcf T hT).2.2.1; have := (hS T hT).2.1
    have : 0 < p + uT p c s a (W T) T - bT p c s a (W T) T := by linarith
    positivity
  have htau : ContinuousOn (fun T => tauF p (W T) (uT p c s a (W T) T) (bT p c s a (W T) T)) S := by
    unfold tauF
    apply ContinuousOn.sub continuousOn_const
    apply Real.continuous_sqrt.comp_continuousOn
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (hg1.sub hg0) hu
    intro T hT; exact (hcf T hT).2.2.1.ne'
  exact (hg0.div_const a).mul htau

noncomputable def eb0 (p c s a : ℝ) : ℝ := (p - c) ^ 2 / (2 * a * (p - s))
noncomputable def kc (p c s a κ T : ℝ) : ℝ :=
  (a * eb0 p c s a ^ 2 / 2 - κ) * ((p - c) ^ 5 - zeta p s a T) /
    ((p - c) ^ 5 * (T * (1 - T / eb0 p c s a)))
noncomputable def Fc (p c s a κ T : ℝ) : ℝ :=
  g0F p (c + kc p c s a κ T) (bT p c s a (c + kc p c s a κ T) T) ^ 2 / (2 * a)

lemma basic_ids (p c s a : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a) :
    0 < eb0 p c s a ∧ T3 p c s a = eb0 p c s a * ((p - c) / (p - s)) ∧
    (∀ T, zeta p s a T = 4 * a ^ 2 * (p - s) ^ 3 * T ^ 2) ∧
    (p - c) ^ 5 = (p - c) / (p - s) * (4 * a ^ 2 * (p - s) ^ 3) * eb0 p c s a ^ 2 ∧
    T3 p c s a < eb0 p c s a := by
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hE : 0 < eb0 p c s a := by unfold eb0; positivity
  have h2 : T3 p c s a = eb0 p c s a * ((p - c) / (p - s)) := by
    unfold T3 eb0; field_simp
  refine ⟨hE, h2, fun T => rfl, by unfold eb0; field_simp; ring, ?_⟩
  rw [h2]
  have : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; linarith
  nlinarith

lemma curve_kappa (p c s a κ T : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hT0 : 0 < T) (hT3 : T ≤ T3 p c s a) :
    a * eb0 p c s a ^ 2 / 2 + uT p c s a (c + kc p c s a κ T) T * T ^ 2 / eb0 p c s a
      - uT p c s a (c + kc p c s a κ T) T * T = κ := by
  obtain ⟨hE, -, -, -, hT3E⟩ := basic_ids p c s a hcp hsc ha
  obtain ⟨h5, -, -, -⟩ := ratio_facts p c s a T hcp hsc ha hT0.le hT3
  have hd : 0 < p - c := by linarith
  have h1 : 0 < 1 - T / eb0 p c s a := by
    have : T / eb0 p c s a < 1 := by rw [div_lt_one hE]; linarith
    linarith
  have hET : eb0 p c s a - T ≠ 0 := by linarith
  unfold uT kc
  simp only [add_sub_cancel_left]
  field_simp
  ring

lemma anti_core (q α E T1 T2 : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hα : 0 < α) (hE : 0 < E)
    (h1 : 0 < T1) (h12 : T1 < T2) (h2 : T2 < E) :
    (q * α * E ^ 2 - α * T2 ^ 2) * (T1 * (E - T1)) < (q * α * E ^ 2 - α * T1 ^ 2) * (T2 * (E - T2)) := by
  have key : (q * α * E ^ 2 - α * T1 ^ 2) * (T2 * (E - T2)) - (q * α * E ^ 2 - α * T2 ^ 2) * (T1 * (E - T1))
      = (T2 - T1) * α * E * (q * (E - T1) * (E - T2) + (1 - q) * T1 * T2) := by ring
  have : 0 < (T2 - T1) * α * E * (q * (E - T1) * (E - T2) + (1 - q) * T1 * T2) := by
    have : 0 < q * (E - T1) * (E - T2) := by
      have : 0 < E - T1 := by linarith
      have : 0 < E - T2 := by linarith
      positivity
    have : 0 < (1 - q) * T1 * T2 := by
      have : 0 < 1 - q := by linarith
      have : 0 < T2 := by linarith
      positivity
    have : 0 < T2 - T1 := by linarith
    positivity
  linarith

lemma kc_anti (p c s a κ T1 T2 : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hκ : κ < a * eb0 p c s a ^ 2 / 2) (h1 : 0 < T1) (h12 : T1 < T2) (h2 : T2 ≤ T3 p c s a) :
    kc p c s a κ T2 < kc p c s a κ T1 := by
  obtain ⟨hE, hT3q, hz, h5, hT3E⟩ := basic_ids p c s a hcp hsc ha
  unfold kc
  rw [hz T1, hz T2, h5]
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hq0 : 0 < (p - c) / (p - s) := div_pos hd hD
  have hq1 : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; linarith
  set E := eb0 p c s a
  set q := (p - c) / (p - s)
  set α := 4 * a ^ 2 * (p - s) ^ 3 with hα
  have hαpos : 0 < α := by positivity
  have hcore := anti_core q α E T1 T2 hq0 hq1 hαpos hE h1 h12 (by linarith)
  have hC : 0 < a * E ^ 2 / 2 - κ := by linarith
  have e : ∀ T, 0 < T → T < E → (a * E ^ 2 / 2 - κ) * (q * α * E ^ 2 - α * T ^ 2) /
      (q * α * E ^ 2 * (T * (1 - T / E))) =
      (a * E ^ 2 / 2 - κ) / (q * α * E) * ((q * α * E ^ 2 - α * T ^ 2) / (T * (E - T))) := by
    intro T hT hTE
    have : E - T ≠ 0 := by linarith
    field_simp
  rw [e T1 h1 (by linarith), e T2 (by linarith) (by linarith)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  linarith

lemma T3_vals (p c s a κ : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a) (hκ0 : 0 < κ)
    (hκ : κ < a * eb0 p c s a ^ 2 / 2) :
    kc p c s a κ (T3 p c s a) < p - c ∧ 0 < kc p c s a κ (T3 p c s a) ∧ κ < Fc p c s a κ (T3 p c s a) := by
  obtain ⟨hE, hT3q, hz, h5, hT3E⟩ := basic_ids p c s a hcp hsc ha
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hk : kc p c s a κ (T3 p c s a) = (a * eb0 p c s a ^ 2 / 2 - κ) / T3 p c s a := by
    unfold kc
    rw [hz, h5, hT3q]
    have hq1 : (p - c) / (p - s) < 1 := by rw [div_lt_one hD]; linarith
    generalize (p - c) / (p - s) = q at *
    generalize eb0 p c s a = E at *
    have hq0 : 0 < q := by
      by_contra hc; rw [not_lt] at hc
      have : q * (4 * a ^ 2 * (p - s) ^ 3) * E ^ 2 ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg _ (by positivity)
        exact mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
      have : 0 < (p - c) ^ 5 := by positivity
      linarith
    have e1 : q * (4 * a ^ 2 * (p - s) ^ 3) * E ^ 2 - 4 * a ^ 2 * (p - s) ^ 3 * (E * q) ^ 2
        = q * (4 * a ^ 2 * (p - s) ^ 3) * E ^ 2 * (1 - q) := by ring
    have e2 : 1 - E * q / E = 1 - q := by field_simp
    rw [e1, e2]
    have : 1 - q ≠ 0 := by linarith
    field_simp
  have hPi : a * eb0 p c s a ^ 2 / 2 = (p - c) / 4 * T3 p c s a := by
    unfold eb0 T3; field_simp; ring
  have hT3pos : 0 < T3 p c s a := by unfold T3; positivity
  set y := kc p c s a κ (T3 p c s a) / (p - c) with hy
  have hky : kc p c s a κ (T3 p c s a) = (p - c) * y := by rw [hy]; field_simp
  have hy0 : 0 < y := by
    rw [hy, hk]; apply div_pos (div_pos (by linarith) hT3pos) hd
  have hy4 : y < 1 / 4 := by
    rw [hy, hk, hPi, div_div, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨by rw [hky]; nlinarith, by rw [hky]; positivity, ?_⟩
  have hb : bT p c s a (c + kc p c s a κ (T3 p c s a)) (T3 p c s a) = s := by
    unfold bT
    rw [hz, show (p - c) ^ 6 - (p - s) * (4 * a ^ 2 * (p - s) ^ 3 * T3 p c s a ^ 2) = 0 by
      unfold T3; field_simp; ring]
    simp
  have hκy : κ = a * eb0 p c s a ^ 2 / 2 * (1 - 4 * y) := by
    rw [hy, hk, hPi]; field_simp; ring
  unfold Fc g0F
  rw [hb, hky, hκy]
  have hF : (p - (c + (p - c) * y)) ^ 2 / (2 * (p - s)) = (p - c) ^ 2 * (1 - y) ^ 2 / (2 * (p - s)) := by
    ring
  rw [hF]
  have : a * eb0 p c s a ^ 2 / 2 = (p - c) ^ 4 / (8 * a * (p - s) ^ 2) := by
    unfold eb0; field_simp; ring
  rw [this]
  have e : ((p - c) ^ 2 * (1 - y) ^ 2 / (2 * (p - s))) ^ 2 / (2 * a)
      = (p - c) ^ 4 / (8 * a * (p - s) ^ 2) * (1 - y) ^ 4 := by
    field_simp; ring
  rw [e]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  nlinarith [sq_nonneg y, mul_pos hy0 hy0, mul_pos (mul_pos hy0 hy0) hy0]

lemma Ts_val (p c s a κ : ℝ) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (hκ : κ < a * eb0 p c s a ^ 2 / 2) :
    let Ts := min (T3 p c s a / 2) (3 * (a * eb0 p c s a ^ 2 / 2 - κ) / (4 * (p - c)))
    0 < Ts ∧ Ts < T3 p c s a ∧ p - c ≤ kc p c s a κ Ts := by
  intro Ts
  obtain ⟨hE, hT3q, hz, h5, hT3E⟩ := basic_ids p c s a hcp hsc ha
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hT3pos : 0 < T3 p c s a := by unfold T3; positivity
  have hC : 0 < a * eb0 p c s a ^ 2 / 2 - κ := by linarith
  have hTs0 : 0 < Ts := lt_min (by linarith) (by positivity)
  have hTs1 : Ts ≤ T3 p c s a / 2 := min_le_left _ _
  have hTs2 : Ts ≤ 3 * (a * eb0 p c s a ^ 2 / 2 - κ) / (4 * (p - c)) := min_le_right _ _
  refine ⟨hTs0, by linarith, ?_⟩
  have hfac : 0 < 1 - Ts / eb0 p c s a := by
    have : Ts / eb0 p c s a < 1 := by rw [div_lt_one hE]; linarith
    linarith
  have hfac1 : 1 - Ts / eb0 p c s a ≤ 1 := by
    have : 0 ≤ Ts / eb0 p c s a := div_nonneg hTs0.le hE.le
    linarith
  unfold kc
  rw [le_div_iff₀ (by positivity)]
  set C := a * eb0 p c s a ^ 2 / 2 - κ
  set E := eb0 p c s a
  set q := (p - c) / (p - s)
  have hq1 : q < 1 := by rw [div_lt_one hD]; linarith
  have hq0 : 0 < q := div_pos hd hD
  have hα : 0 < 4 * a ^ 2 * (p - s) ^ 3 := by positivity
  -- z ≤ d^5 / 4
  have hz4 : zeta p s a Ts ≤ (p - c) ^ 5 / 4 := by
    rw [hz, h5]
    have : Ts ^ 2 ≤ (E * q / 2) ^ 2 := by
      rw [hT3q] at hTs1; exact pow_le_pow_left₀ hTs0.le hTs1 2
    have : 4 * a ^ 2 * (p - s) ^ 3 * Ts ^ 2 ≤ 4 * a ^ 2 * (p - s) ^ 3 * (E * q / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left this hα.le
    have : q * q ≤ q := by nlinarith
    have : 0 ≤ 4 * a ^ 2 * (p - s) ^ 3 * E ^ 2 := by positivity
    nlinarith
  have h1 : (p - c) * ((p - c) ^ 5 * (Ts * (1 - Ts / E))) ≤ (p - c) * ((p - c) ^ 5 * Ts) := by
    apply mul_le_mul_of_nonneg_left _ hd.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have h2 : (p - c) * Ts ≤ 3 * C / 4 := by
    rw [le_div_iff₀ (by positivity)] at hTs2; linarith
  have h3 : 3 * (p - c) ^ 5 / 4 ≤ (p - c) ^ 5 - zeta p s a Ts := by linarith
  have h4 : (p - c) * ((p - c) ^ 5 * Ts) ≤ C * ((p - c) ^ 5 - zeta p s a Ts) := by
    have : (p - c) * ((p - c) ^ 5 * Ts) = (p - c) ^ 5 * ((p - c) * Ts) := by ring
    rw [this]
    have h5' : (p - c) ^ 5 * ((p - c) * Ts) ≤ (p - c) ^ 5 * (3 * C / 4) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : (p - c) ^ 5 * (3 * C / 4) = C * (3 * (p - c) ^ 5 / 4) := by ring
    have h7 : C * (3 * (p - c) ^ 5 / 4) ≤ C * ((p - c) ^ 5 - zeta p s a Ts) :=
      mul_le_mul_of_nonneg_left h3 hC.le
    linarith
  linarith

end CRET2

open ChannelRebate.Effort CachonCoord.Newsvendor CRET2 in
theorem solution
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < κ →
      ∃ w T : ℝ, c < w ∧ w < p ∧
        (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) ∧
        IsLlow p c s a w T (κ - ε) ∧ IsLbar p c s a w T κ := by
  obtain ⟨hQbv, hebv⟩ := ebar_val p c s a Qb hcp hsc ha hQb
  have hebv' : ebarOf p s a Qb = eb0 p c s a := hebv
  have hκ' : κ < a * eb0 p c s a ^ 2 / 2 := by
    rw [hebv'] at hκPi; unfold Lam V at hκPi; linarith
  obtain ⟨hE, hT3q, hz, h5, hT3E⟩ := basic_ids p c s a hcp hsc ha
  have hd : 0 < p - c := by linarith
  have hD : 0 < p - s := by linarith
  have hT3pos : 0 < T3 p c s a := by unfold T3; positivity
  obtain ⟨hTs0, hTsT3, hkTs⟩ := Ts_val p c s a κ hcp hsc ha hκ'
  set Ts := min (T3 p c s a / 2) (3 * (a * eb0 p c s a ^ 2 / 2 - κ) / (4 * (p - c))) with hTsdef
  obtain ⟨hk3, hk3pos, hF3⟩ := T3_vals p c s a κ hcp hsc ha hκ0 hκ'
  set K := kc p c s a κ with hKdef
  -- positivity and continuity of K on (0, T3]
  have hfac : ∀ T, 0 < T → T ≤ T3 p c s a → 0 < 1 - T / eb0 p c s a := by
    intro T hT0 hT3
    have : T / eb0 p c s a < 1 := by rw [div_lt_one hE]; linarith
    linarith
  have hKpos : ∀ T, 0 < T → T ≤ T3 p c s a → 0 < K T := by
    intro T hT0 hT3
    obtain ⟨h5', -, -, -⟩ := ratio_facts p c s a T hcp hsc ha hT0.le hT3
    have := hfac T hT0 hT3
    rw [hKdef]; unfold kc
    apply div_pos (mul_pos (by linarith) h5') (by positivity)
  have hKcont : ∀ t, 0 < t → ContinuousOn K (Set.Icc t (T3 p c s a)) := by
    intro t ht
    rw [hKdef]; unfold kc zeta
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro T hT
    have := hfac T (by linarith [hT.1]) hT.2
    have : 0 < T := by linarith [hT.1]
    positivity
  -- T_L with K T_L = d
  obtain ⟨TL, hTL, hKTL⟩ := intermediate_value_Icc' hTsT3.le (hKcont Ts hTs0)
    (show p - c ∈ Set.Icc (K (T3 p c s a)) (K Ts) from ⟨hk3.le, hkTs⟩)
  have hTL0 : 0 < TL := lt_of_lt_of_le hTs0 hTL.1
  have hTLT3 : TL < T3 p c s a := by
    rcases hTL.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hKTL; linarith
  have hKlt : ∀ T, TL < T → T ≤ T3 p c s a → K T < p - c := by
    intro T h1 h2; rw [← hKTL]; exact kc_anti p c s a κ TL T hcp hsc ha hκ' hTL0 h1 h2
  set S := Set.Icc TL (T3 p c s a) with hSdef
  have hWcont : ContinuousOn (fun T => c + K T) S :=
    continuousOn_const.add (hKcont TL hTL0)
  have hSprop : ∀ T ∈ S, c ≤ c + K T ∧ c + K T ≤ p ∧ 0 ≤ T ∧ T ≤ T3 p c s a := by
    intro T hT
    have hT0 : 0 < T := lt_of_lt_of_le hTL0 hT.1
    refine ⟨by linarith [hKpos T hT0 hT.2], ?_, hT0.le, hT.2⟩
    rcases hT.1.lt_or_eq with h | h
    · linarith [hKlt T h hT.2]
    · rw [← h, hKTL]; linarith
  have hFcont : ContinuousOn (Fc p c s a κ) S := by
    have := curve_cont p c s a (fun T => c + K T) S hcp hsc ha hWcont hSprop
    exact (this.pow 2).div_const _
  have hFTL : Fc p c s a κ TL = 0 := by
    unfold Fc g0F; rw [← hKdef, hKTL]; simp
  -- first crossing
  set A := S ∩ Fc p c s a κ ⁻¹' Set.Ici κ with hAdef
  have hAcl : IsClosed A := hFcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hT3A : T3 p c s a ∈ A := ⟨⟨hTLT3.le, le_rfl⟩, hF3.le⟩
  have hAne : A.Nonempty := ⟨_, hT3A⟩
  have hAbdd : BddBelow A := ⟨TL, fun x hx => hx.1.1⟩
  set T0 := sInf A with hT0def
  have hT0A : T0 ∈ A := hAcl.csInf_mem hAne hAbdd
  have hFT0 : Fc p c s a κ T0 = κ := by
    obtain ⟨T', hT', hFT'⟩ := intermediate_value_Icc hT0A.1.1
      (hFcont.mono (Set.Icc_subset_Icc le_rfl hT0A.1.2))
      (show κ ∈ Set.Icc (Fc p c s a κ TL) (Fc p c s a κ T0) from
        ⟨by rw [hFTL]; linarith, hT0A.2⟩)
    have hT'A : T' ∈ A := by
      refine ⟨⟨hT'.1, hT'.2.trans hT0A.1.2⟩, ?_⟩
      show κ ≤ Fc p c s a κ T'
      rw [hFT']
    have : T0 ≤ T' := csInf_le hAbdd hT'A
    have : T' = T0 := le_antisymm hT'.2 this
    rw [← this, hFT']
  have hTLT0 : TL < T0 := by
    rcases hT0A.1.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hFTL] at hFT0; linarith
  have hT0T3 : T0 < T3 p c s a := by
    rcases hT0A.1.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hFT0; linarith
  have hbelow : ∀ T, TL ≤ T → T < T0 → Fc p c s a κ T < κ := by
    intro T h1 h2
    by_contra hc; rw [not_lt] at hc
    have : T ∈ A := ⟨⟨h1, by linarith⟩, hc⟩
    have := csInf_le hAbdd this
    linarith
  -- margin at T0
  have hT00 : 0 < T0 := hTL0.trans hTLT0
  have hw0 : c < c + K T0 := by linarith [hKpos T0 hT00 hT0T3.le]
  have hw0p : c + K T0 < p := by linarith [hKlt T0 hTLT0 hT0T3.le]
  have hκT : ∀ T, 0 < T → T ≤ T3 p c s a →
      a * ebarOf p s a Qb ^ 2 / 2 + uT p c s a (c + K T) T * T ^ 2 / ebarOf p s a Qb
        - uT p c s a (c + K T) T * T = κ := by
    intro T h0 h3; rw [hebv', hKdef]; exact curve_kappa p c s a κ T hcp hsc ha h0 h3
  have hm0 : m1F p c s a (c + K T0) T0 < T0 :=
    crossing p c s a Qb (c + K T0) T0 κ hcp hsc ha hw0 hw0p hQb hT00 hT0T3
      (hκT T0 hT00 hT0T3.le) hFT0 (by rw [hebv']; exact hκ')
  -- continuity of the margin near T0
  set S' := Set.Ioo TL (T3 p c s a) with hS'def
  have hMcont : ContinuousOn (fun T => m1F p c s a (c + K T) T) S' := by
    apply curve_cont_m1 p c s a (fun T => c + K T) S' hcp hsc ha
      (hWcont.mono Set.Ioo_subset_Icc_self)
    intro T hT
    have hT0 : 0 < T := hTL0.trans hT.1
    exact ⟨by linarith [hKpos T hT0 hT.2.le], by linarith [hKlt T hT.1 hT.2.le], hT0.le, hT.2.le⟩
  have hMat : ContinuousAt (fun T => m1F p c s a (c + K T) T) T0 :=
    hMcont.continuousAt (isOpen_Ioo.mem_nhds ⟨hTLT0, hT0T3⟩)
  have hev : ∀ᶠ T in 𝓝 T0, m1F p c s a (c + K T) T < T :=
    hMat.eventually_lt continuousAt_id hm0
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.1 hev
  set α := max TL (T0 - δ / 2) with hαdef
  have hαT0 : α < T0 := max_lt hTLT0 (by linarith)
  have hαTL : TL ≤ α := le_max_left _ _
  have hFα : Fc p c s a κ α < κ := hbelow α hαTL hαT0
  refine ⟨κ - Fc p c s a κ α, by linarith, fun ε hε hεε₀ hεκ => ?_⟩
  obtain ⟨T, hT, hFT⟩ := intermediate_value_Icc hαT0.le
    (hFcont.mono (Set.Icc_subset_Icc hαTL hT0A.1.2))
    (show κ - ε ∈ Set.Icc (Fc p c s a κ α) (Fc p c s a κ T0) from ⟨by linarith, by linarith⟩)
  have hTT0 : T < T0 := by
    rcases hT.2.lt_or_eq with h | h
    · exact h
    · rw [h, hFT0] at hFT; linarith
  have hTLT : TL < T := by
    rcases (hαTL.trans hT.1).lt_or_eq with h | h
    · exact h
    · rw [← h, hFTL] at hFT; linarith
  have hTpos : 0 < T := hTL0.trans hTLT
  have hTT3 : T < T3 p c s a := hTT0.trans hT0T3
  have hwc : c < c + K T := by linarith [hKpos T hTpos hTT3.le]
  have hwp : c + K T < p := by linarith [hKlt T hTLT hTT3.le]
  have hmT : m1F p c s a (c + K T) T < T := by
    apply hδball
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : T0 - δ / 2 ≤ α := le_max_right _ _
      linarith [hT.1]
    · linarith
  have hFT' : g0F p (c + K T) (bT p c s a (c + K T) T) ^ 2 / (2 * a) = κ - ε := hFT
  obtain ⟨h1, h2, h3⟩ := point_ok p c s a Qb (c + K T) T κ (κ - ε) hcp hsc ha hwc hwp hQb
    hTpos hTT3 (hκT T hTpos hTT3.le) hFT' (by linarith) hmT
  exact ⟨c + K T, T, hwc, hwp, h3, h1, h2⟩

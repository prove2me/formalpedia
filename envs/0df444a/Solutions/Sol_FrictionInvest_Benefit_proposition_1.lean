-- Prove2me | solution 1 for FrictionInvest.Benefit.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:17:25.815663+00:00
-- url     : https://prove2.me/submissions/15a71e3c-97f5-4e0b-a093-d43762b1828f

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

open FrictionInvest.Benefit

namespace FIP4Help

lemma revInt_le (P : Params) (q : ℝ) (hq0 : 0 ≤ q) (hqa : q ≤ P.a) :
    ∫ ξ in (0)..P.a, revenue P q ξ = P.p * q ^ 2 / 2 + P.p * q * (P.a - q) := by
  have hc : Continuous (fun ξ => revenue P q ξ) := by
    unfold revenue; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := q)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ ξ in (0)..q, revenue P q ξ = ∫ ξ in (0)..q, P.p * ξ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hq0] at hx
    simp [revenue, min_eq_right hx.2]
  have h2 : ∫ ξ in q..P.a, revenue P q ξ = ∫ ξ in q..P.a, P.p * q := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hqa] at hx
    simp [revenue, min_eq_left hx.1]
  rw [h1, h2, intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp; ring

lemma revInt_ge (P : Params) (q : ℝ) (hqa : P.a ≤ q) (ha : 0 ≤ P.a) :
    ∫ ξ in (0)..P.a, revenue P q ξ = P.p * P.a ^ 2 / 2 := by
  have : ∫ ξ in (0)..P.a, revenue P q ξ = ∫ ξ in (0)..P.a, P.p * ξ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    simp [revenue, min_eq_right (hx.2.trans hqa)]
  rw [this, intervalIntegral.integral_const_mul, integral_id]; ring

lemma bankInt (P : Params) (hp : 0 < P.p) (γ q F : ℝ) (hq : 0 ≤ q) (hF0 : 0 ≤ F)
    (hFa : F ≤ P.a * P.p) (hcase : F = 0 ∨ F < P.p * q ∨ P.a ≤ q) :
    ∫ ξ in (0)..P.a, γ * revenue P q ξ * (if revenue P q ξ ≤ F then 1 else 0)
      = γ * P.p * (F / P.p) ^ 2 / 2 := by
  set f : ℝ → ℝ := fun ξ => γ * revenue P q ξ * (if revenue P q ξ ≤ F then (1:ℝ) else 0)
    with hf
  set b := F / P.p with hb
  have hb0 : 0 ≤ b := div_nonneg hF0 hp.le
  have hba : b ≤ P.a := by rw [hb, div_le_iff₀ hp]; linarith
  have e1 : ∀ x ∈ Set.Ioc 0 b, f x = γ * P.p * x := by
    intro x hx
    have hxq : x ≤ q := by
      rcases hcase with h | h | h
      · exfalso
        have : b = 0 := by rw [hb, h, zero_div]
        linarith [hx.1, hx.2]
      · have : b < q := by rw [hb, div_lt_iff₀ hp]; linarith
        linarith [hx.2]
      · linarith [hx.2]
    have hle : P.p * x ≤ F := by
      have := hx.2; rw [hb, le_div_iff₀ hp] at this; linarith
    simp only [hf, revenue, min_eq_right hxq, if_pos hle]; ring
  have e2 : ∀ x ∈ Set.Ioc b P.a, f x = 0 := by
    intro x hx
    have hgt : F < P.p * x := by
      have := hx.1; rw [hb, div_lt_iff₀ hp] at this; linarith
    have hr : revenue P q x = P.p * min q x := rfl
    simp only [hf]; rw [hr]
    rcases le_or_gt x q with hxq | hxq
    · rw [min_eq_right hxq, if_neg (not_le.mpr hgt)]; ring
    · rw [min_eq_left hxq.le]
      rcases hcase with h | h | h
      · split_ifs with h'
        · have : P.p * q = 0 := le_antisymm (h ▸ h') (mul_nonneg hp.le hq)
          rw [this]; ring
        · ring
      · rw [if_neg (not_le.mpr h)]; ring
      · exfalso; linarith [hx.2]
  have hi1 : IntervalIntegrable f MeasureTheory.volume 0 b := by
    have hc : Continuous (fun x : ℝ => γ * P.p * x) := by fun_prop
    apply (hc.intervalIntegrable 0 b).congr
    rw [Set.uIoc_of_le hb0]
    intro x hx; exact (e1 x hx).symm
  have hi2 : IntervalIntegrable f MeasureTheory.volume b P.a := by
    apply (intervalIntegrable_const (c := (0:ℝ))).congr
    rw [Set.uIoc_of_le hba]
    intro x hx; exact (e2 x hx).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have j1 : ∫ x in (0)..b, f x = ∫ x in (0)..b, γ * P.p * x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hb0] at hx
    exact e1 x hx
  have j2 : ∫ x in b..P.a, f x = ∫ x in b..P.a, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hba] at hx
    exact e2 x hx
  rw [j1, j2, intervalIntegral.integral_const_mul, integral_id]
  simp; ring

noncomputable def Fg (P : Params) (γ c y x : ℝ) : ℝ :=
  P.a * P.p / (1 + γ) * (1 - Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)))

lemma fv_eq (P : Params) (γ c y x : ℝ) (h : y ≤ c * x) : faceValue P γ c y x = Fg P γ c y x := by
  unfold faceValue Fg
  split_ifs with h'
  · have : c * x - y = 0 := by linarith
    simp [this]
  · rfl

lemma fv_zero (P : Params) (γ c y x : ℝ) (h : c * x ≤ y) : faceValue P γ c y x = 0 := by
  unfold faceValue; rw [if_pos h]

lemma Fg_cont (P : Params) (γ c y : ℝ) : Continuous (fun x => Fg P γ c y x) := by
  unfold Fg; fun_prop

lemma mceInt (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 < c) (hq : 0 ≤ q) (hy : 0 ≤ y)
    (hcase : c * q ≤ y ∨ 2 * (1 + γ) * (c * q - y) < P.a * P.p) :
    ∫ x in (0)..q, mce P γ c y x = γ * faceValue P γ c y q ^ 2 / (2 * P.a * P.p) := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  by_cases hcq : c * q ≤ y
  · rw [fv_zero P γ c y q hcq]
    have : ∫ x in (0)..q, mce P γ c y x = ∫ x in (0)..q, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hq] at hx
      have : c * x ≤ y := by nlinarith [hx.2]
      simp [mce, fv_zero P γ c y x this]
    rw [this]; simp
  have hlend : 2 * (1 + γ) * (c * q - y) < P.a * P.p := hcase.resolve_left hcq
  push_neg at hcq
  set s := y / c with hs
  have hs0 : 0 ≤ s := div_nonneg hy hc.le
  have hcs : c * s = y := by rw [hs]; field_simp
  have hsq : s < q := by
    by_contra h; push_neg at h; nlinarith
  -- u positive on [s, q]
  have hupos : ∀ x, x ≤ q → 0 < 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p) := by
    intro x hx
    have : 2 * (1 + γ) * (c * x - y) / (P.a * P.p) < 1 := by
      rw [div_lt_one hap]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right (mul_le_mul_of_nonneg_left hx hc.le) y)
        (by linarith : (0:ℝ) ≤ 2 * (1 + γ))
      linarith
    linarith
  have hden : ∀ x, x ≤ q →
      P.a * P.p - (1 + γ) * Fg P γ c y x
        = P.a * P.p * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) := by
    intro x _
    unfold Fg; field_simp; ring
  have hdenpos : ∀ x, x ≤ q → 0 < P.a * P.p - (1 + γ) * Fg P γ c y x := by
    intro x hx; rw [hden x hx]
    exact mul_pos hap (Real.sqrt_pos.mpr (hupos x hx))
  set g : ℝ → ℝ := fun x => γ * c * Fg P γ c y x / (P.a * P.p - (1 + γ) * Fg P γ c y x) with hg
  have hgc : ContinuousOn g (Set.Icc s q) := by
    apply ContinuousOn.div
    · exact (continuous_const.mul (Fg_cont P γ c y)).continuousOn
    · exact (continuous_const.sub (continuous_const.mul (Fg_cont P γ c y))).continuousOn
    · intro x hx; exact (hdenpos x hx.2).ne'
  have e2 : Set.EqOn (fun x => mce P γ c y x) g (Set.uIcc s q) := by
    intro x hx
    rw [Set.uIcc_of_le hsq.le] at hx
    have : y ≤ c * x := by rw [← hcs]; nlinarith [hx.1]
    simp only [mce, hg, fv_eq P γ c y x this]
  have e1 : Set.EqOn (fun x => mce P γ c y x) (fun _ => (0:ℝ)) (Set.uIcc 0 s) := by
    intro x hx
    rw [Set.uIcc_of_le hs0] at hx
    have : c * x ≤ y := by rw [← hcs]; nlinarith [hx.2]
    simp [mce, fv_zero P γ c y x this]
  have hi1 : IntervalIntegrable (fun x => mce P γ c y x) MeasureTheory.volume 0 s :=
    (continuousOn_const.congr e1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => mce P γ c y x) MeasureTheory.volume s q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hsq.le] at e2 ⊢
    exact hgc.congr e2
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2]
  simp only [intervalIntegral.integral_zero, zero_add]
  have hFTC : ∫ x in s..q, g x
      = γ * Fg P γ c y q ^ 2 / (2 * P.a * P.p) - γ * Fg P γ c y s ^ 2 / (2 * P.a * P.p) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsq.le
    · exact (Continuous.continuousOn (by have := Fg_cont P γ c y; fun_prop))
    · intro x hx
      have hux := hupos x hx.2.le
      have hu : HasDerivAt (fun x => 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p))
          (-(2 * (1 + γ) * (c * 1) / (P.a * P.p))) x :=
        ((((hasDerivAt_id x).const_mul c).sub_const y).const_mul (2 * (1 + γ))
          |>.div_const (P.a * P.p)).const_sub 1
      have hF : HasDerivAt (fun x => Fg P γ c y x)
          (P.a * P.p / (1 + γ) * (-((-(2 * (1 + γ) * (c * 1) / (P.a * P.p))) /
            (2 * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)))))) x :=
        ((hu.sqrt hux.ne').const_sub 1).const_mul (P.a * P.p / (1 + γ))
      have hH := ((hF.pow 2).const_mul γ).div_const (2 * P.a * P.p)
      refine hH.congr_deriv ?_
      · have hd := hden x hx.2.le
        have hdp := hdenpos x hx.2.le
        simp only [hg]
        rw [hd] at hdp ⊢
        have hr := Real.sqrt_pos.mpr hux
        set r := Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) with hr'
        have h1g : (1 + γ) ≠ 0 := by linarith
        field_simp
        ring
    · exact hgc.intervalIntegrable_of_Icc hsq.le
  rw [hFTC, fv_eq P γ c y q hcq.le]
  have : Fg P γ c y s = 0 := by
    unfold Fg; rw [hcs]; simp
  rw [this]; ring

lemma Fg_bounds (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y x : ℝ) (hγ : 0 ≤ γ)
    (h1 : y ≤ c * x) (h2 : 2 * (1 + γ) * (c * x - y) < P.a * P.p) :
    0 ≤ Fg P γ c y x ∧ Fg P γ c y x < P.a * P.p / (1 + γ) := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hu1 : 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p) ≤ 1 := by
    have : 0 ≤ 2 * (1 + γ) * (c * x - y) / (P.a * P.p) := by
      apply div_nonneg _ hap.le; nlinarith
    linarith
  have hu0 : 0 < 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p) := by
    have : 2 * (1 + γ) * (c * x - y) / (P.a * P.p) < 1 := by rw [div_lt_one hap]; exact h2
    linarith
  have hs1 : Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hu1
  have hs0 := Real.sqrt_pos.mpr hu0
  have hK : 0 < P.a * P.p / (1 + γ) := div_pos hap (by linarith)
  unfold Fg
  constructor
  · exact mul_nonneg hK.le (by linarith)
  · nlinarith

lemma fv_props (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hF : Feasible P γ c y q) :
    0 ≤ faceValue P γ c y q ∧ faceValue P γ c y q ≤ P.a * P.p ∧
      (faceValue P γ c y q = 0 ∨ faceValue P γ c y q < P.p * q) := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  by_cases hcq : c * q ≤ y
  · rw [fv_zero P γ c y q hcq]; exact ⟨le_rfl, hap.le, Or.inl rfl⟩
  · have h := hF.2.resolve_left hcq
    push_neg at hcq
    rw [fv_eq P γ c y q hcq.le] at h ⊢
    obtain ⟨b0, b1⟩ := Fg_bounds P hp ha γ c y q hγ hcq.le h.1
    have : P.a * P.p / (1 + γ) ≤ P.a * P.p := div_le_self hap.le (by linarith)
    refine ⟨b0, by linarith, Or.inr (by linarith [h.2])⟩

lemma bankCost_eq (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hF : Feasible P γ c y q) (hcase : faceValue P γ c y q = 0 ∨
      faceValue P γ c y q < P.p * q ∨ P.a ≤ q) :
    bankCost P γ c y q = γ * faceValue P γ c y q ^ 2 / (2 * P.a * P.p) := by
  obtain ⟨h0, h1, _⟩ := fv_props P hp ha γ c y q hγ hF
  unfold bankCost
  rw [bankInt P hp γ q _ hF.1 h0 h1 hcase]
  field_simp

/-- Profit identity for feasible quantities below `a`. -/
lemma profit_eq (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 < c) (hy : 0 ≤ y) (hF : Feasible P γ c y q) (hqa : q ≤ P.a) :
    expProfit P γ c y q = (P.p * q - P.p * q ^ 2 / (2 * P.a) - c * q)
      - ∫ x in (0)..q, mce P γ c y x := by
  have hcase : c * q ≤ y ∨ 2 * (1 + γ) * (c * q - y) < P.a * P.p := by
    rcases hF.2 with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  rw [mceInt P hp ha γ c y q hγ hc hF.1 hy hcase]
  unfold expProfit
  obtain ⟨_, _, h2⟩ := fv_props P hp ha γ c y q hγ hF
  rw [bankCost_eq P hp ha γ c y q hγ hF (h2.elim Or.inl (fun h => Or.inr (Or.inl h))),
    revInt_le P q hF.1 hqa]
  field_simp; ring

lemma fv_mono (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y x q : ℝ) (hγ : 0 ≤ γ)
    (hxq : x ≤ q) (hc : 0 < c) (hF : Feasible P γ c y q) :
    faceValue P γ c y x ≤ faceValue P γ c y q := by
  obtain ⟨hq0, _, _⟩ := fv_props P hp ha γ c y q hγ hF
  by_cases hx : c * x ≤ y
  · rw [fv_zero P γ c y x hx]; exact hq0
  push_neg at hx
  have hq : y < c * q := lt_of_lt_of_le hx (mul_le_mul_of_nonneg_left hxq hc.le)
  rw [fv_eq P γ c y x hx.le, fv_eq P γ c y q hq.le]
  unfold Fg
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hK : 0 < P.a * P.p / (1 + γ) := div_pos hap (by linarith)
  apply mul_le_mul_of_nonneg_left _ hK.le
  have : Real.sqrt (1 - 2 * (1 + γ) * (c * q - y) / (P.a * P.p))
      ≤ Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) := by
    apply Real.sqrt_le_sqrt
    have : 2 * (1 + γ) * (c * x - y) ≤ 2 * (1 + γ) * (c * q - y) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    have := div_le_div_of_nonneg_right this hap.le
    linarith
  linarith

lemma eq_le_a (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 < c) (h : IsEqQuantity P γ c y q) : q ≤ P.a := by
  by_contra hqa
  push_neg at hqa
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hFa : Feasible P γ c y P.a := by
    refine ⟨ha.le, ?_⟩
    by_cases hca : c * P.a ≤ y
    · exact Or.inl hca
    · right
      push_neg at hca
      have hcq : ¬ c * q ≤ y := by
        intro h'; have := mul_lt_mul_of_pos_left hqa hc; linarith
      have hl := (h.1.2.resolve_left hcq).1
      have h2 : 2 * (1 + γ) * (c * P.a - y) < P.a * P.p := by
        have : 2 * (1 + γ) * (c * P.a - y) ≤ 2 * (1 + γ) * (c * q - y) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        linarith
      refine ⟨h2, ?_⟩
      rw [fv_eq P γ c y P.a hca.le]
      have := (Fg_bounds P hp ha γ c y P.a hγ hca.le h2).2
      have : P.a * P.p / (1 + γ) ≤ P.a * P.p := div_le_self hap.le (by linarith)
      nlinarith
  have hle := h.2 P.a hFa
  have hmono := fv_mono P hp ha γ c y P.a q hγ hqa.le hc h.1
  have e1 := bankCost_eq P hp ha γ c y q hγ h.1 (Or.inr (Or.inr hqa.le))
  have e2 := bankCost_eq P hp ha γ c y P.a hγ hFa (Or.inr (Or.inr le_rfl))
  obtain ⟨f0, _, _⟩ := fv_props P hp ha γ c y P.a hγ hFa
  unfold expProfit at hle
  rw [e1, e2, revInt_ge P q hqa.le ha.le, revInt_ge P P.a le_rfl ha.le] at hle
  have : γ * faceValue P γ c y P.a ^ 2 / (2 * P.a * P.p)
      ≤ γ * faceValue P γ c y q ^ 2 / (2 * P.a * P.p) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hγ
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hqa hc]

lemma bank_zero (P : Params) (c y q : ℝ) : bankCost P 0 c y q = 0 := by
  unfold bankCost; simp

lemma perfect (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (c y q : ℝ) (hc : 0 < c)
    (hcp : c < P.p) (hy : 0 ≤ y) (h : IsEqQuantity P 0 c y q) :
    expProfit P 0 c y q = P.a * (P.p - c) ^ 2 / (2 * P.p) := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  set Q := P.a * (P.p - c) / P.p with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (mul_nonneg ha.le (by linarith)) hp.le
  have hQa : Q ≤ P.a := by rw [hQ, div_le_iff₀ hp]; nlinarith
  have hFQ : Feasible P 0 c y Q := by
    refine ⟨hQ0, ?_⟩
    by_cases hcQ : c * Q ≤ y
    · exact Or.inl hcQ
    right
    push_neg at hcQ
    have hcQ' : c * Q * P.p = P.a * c * (P.p - c) := by rw [hQ]; field_simp
    have h2 : 2 * (1 + 0) * (c * Q - y) < P.a * P.p := by
      have : 2 * (c * Q) * P.p < P.a * P.p * P.p := by
        rw [mul_assoc, hcQ']; nlinarith [sq_nonneg (P.p - 2 * c), mul_pos ha hc]
      have : 2 * (c * Q) < P.a * P.p := lt_of_mul_lt_mul_right this hp.le
      linarith
    refine ⟨h2, ?_⟩
    rw [fv_eq P 0 c y Q hcQ.le]
    unfold Fg
    have hlt : c / P.p < Real.sqrt (1 - 2 * (1 + 0) * (c * Q - y) / (P.a * P.p)) := by
      rw [Real.lt_sqrt (div_nonneg hc.le hp.le)]
      rw [div_pow, div_lt_iff₀ (by positivity)]
      have : 2 * (1 + 0) * (c * Q - y) / (P.a * P.p) * P.p ^ 2
          ≤ 2 * c * (P.p - c) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hap]
        have : (c * Q - y) * P.p ≤ P.a * c * (P.p - c) := by nlinarith
        nlinarith
      have e : (1 - 2 * (1 + 0) * (c * Q - y) / (P.a * P.p)) * P.p ^ 2
          = P.p ^ 2 - 2 * (1 + 0) * (c * Q - y) / (P.a * P.p) * P.p ^ 2 := by ring
      rw [e]; nlinarith [sq_pos_of_pos (sub_pos.mpr hcp)]
    have : P.a * P.p / (1 + 0) * (1 - Real.sqrt (1 - 2 * (1 + 0) * (c * Q - y) / (P.a * P.p)))
        < P.a * P.p / (1 + 0) * (1 - c / P.p) := by
      apply mul_lt_mul_of_pos_left _ (by simpa using hap); linarith
    calc _ < P.a * P.p / (1 + 0) * (1 - c / P.p) := this
      _ = Q * P.p := by rw [hQ]; field_simp; ring
  have hge := h.2 Q hFQ
  have hqa := eq_le_a P hp ha 0 c y q le_rfl hc h
  have hval : ∀ x, 0 ≤ x → x ≤ P.a →
      expProfit P 0 c y x = P.p * x - P.p * x ^ 2 / (2 * P.a) - c * x := by
    intro x hx0 hxa
    unfold expProfit; rw [bank_zero, revInt_le P x hx0 hxa]; field_simp; ring
  rw [hval Q hQ0 hQa] at hge
  rw [hval q h.1.1 hqa] at hge ⊢
  have hQval : P.p * Q - P.p * Q ^ 2 / (2 * P.a) - c * Q = P.a * (P.p - c) ^ 2 / (2 * P.p) := by
    rw [hQ]; field_simp; ring
  rw [hQval] at hge
  apply le_antisymm _ hge
  rw [show P.p * q - P.p * q ^ 2 / (2 * P.a) - c * q = P.a * (P.p - c) ^ 2 / (2 * P.p)
      - P.p / (2 * P.a) * (q - Q) ^ 2 by rw [hQ]; field_simp; ring]
  have : 0 ≤ P.p / (2 * P.a) * (q - Q) ^ 2 := by positivity
  linarith

lemma mrrInt (P : Params) (ha : 0 < P.a) (c u v : ℝ) :
    ∫ x in u..v, mrr P c x = (P.p * v - P.p * v ^ 2 / (2 * P.a) - c * v)
      - (P.p * u - P.p * u ^ 2 / (2 * P.a) - c * u) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have := (((hasDerivAt_id x).const_mul P.p).sub
      (((hasDerivAt_id x).pow 2).const_mul P.p |>.div_const (2 * P.a))).sub
      ((hasDerivAt_id x).const_mul c)
    refine this.congr_deriv ?_
    unfold mrr; simp; field_simp
  · apply Continuous.intervalIntegrable; unfold mrr; fun_prop

end FIP4Help

namespace FIP4L1

open FIP4Help

lemma H_deriv (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y x : ℝ) (hγ : 0 ≤ γ)
    (hux : 0 < 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) :
    HasDerivAt (fun z => γ * Fg P γ c y z ^ 2 / (2 * P.a * P.p))
      (γ * c * Fg P γ c y x / (P.a * P.p - (1 + γ) * Fg P γ c y x)) x := by
  have hd : P.a * P.p - (1 + γ) * Fg P γ c y x
      = P.a * P.p * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) := by
    unfold Fg; field_simp; ring
  have hu : HasDerivAt (fun x => 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p))
      (-(2 * (1 + γ) * (c * 1) / (P.a * P.p))) x :=
    ((((hasDerivAt_id x).const_mul c).sub_const y).const_mul (2 * (1 + γ))
      |>.div_const (P.a * P.p)).const_sub 1
  have hF : HasDerivAt (fun x => Fg P γ c y x)
      (P.a * P.p / (1 + γ) * (-((-(2 * (1 + γ) * (c * 1) / (P.a * P.p))) /
        (2 * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)))))) x :=
    ((hu.sqrt hux.ne').const_sub 1).const_mul (P.a * P.p / (1 + γ))
  have hH := ((hF.pow 2).const_mul γ).div_const (2 * P.a * P.p)
  refine hH.congr_deriv ?_
  rw [hd]
  have hr := Real.sqrt_pos.mpr hux
  set r := Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) with hr'
  have h1g : (1 + γ) ≠ 0 := by linarith
  field_simp
  ring

lemma g_eq (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y x : ℝ) (hγ : 0 ≤ γ)
    (hux : 0 < 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) :
    γ * c * Fg P γ c y x / (P.a * P.p - (1 + γ) * Fg P γ c y x)
      = γ * c / (1 + γ) *
        ((Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)))⁻¹ - 1) := by
  have hd : P.a * P.p - (1 + γ) * Fg P γ c y x
      = P.a * P.p * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) := by
    unfold Fg; field_simp; ring
  rw [hd]
  have hr := Real.sqrt_pos.mpr hux
  set r := Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) with hr'
  have h1g : (1 + γ) ≠ 0 := by linarith
  unfold Fg
  rw [← hr']
  field_simp

end FIP4L1

namespace FIP4P1

open FIP4Help FIP4L1

lemma beyond_a (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 < c) (hF : Feasible P γ c y q) (hqa : P.a < q) :
    Feasible P γ c y P.a ∧ expProfit P γ c y q < expProfit P γ c y P.a := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hFa : Feasible P γ c y P.a := by
    refine ⟨ha.le, ?_⟩
    by_cases hca : c * P.a ≤ y
    · exact Or.inl hca
    · right
      push_neg at hca
      have hcq : ¬ c * q ≤ y := by
        intro h'; have := mul_lt_mul_of_pos_left hqa hc; linarith
      have hl := (hF.2.resolve_left hcq).1
      have h2 : 2 * (1 + γ) * (c * P.a - y) < P.a * P.p := by
        have : 2 * (1 + γ) * (c * P.a - y) ≤ 2 * (1 + γ) * (c * q - y) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
        linarith
      refine ⟨h2, ?_⟩
      rw [fv_eq P γ c y P.a hca.le]
      have := (Fg_bounds P hp ha γ c y P.a hγ hca.le h2).2
      have : P.a * P.p / (1 + γ) ≤ P.a * P.p := div_le_self hap.le (by linarith)
      nlinarith
  refine ⟨hFa, ?_⟩
  have hmono := fv_mono P hp ha γ c y P.a q hγ hqa.le hc hF
  have e1 := bankCost_eq P hp ha γ c y q hγ hF (Or.inr (Or.inr hqa.le))
  have e2 := bankCost_eq P hp ha γ c y P.a hγ hFa (Or.inr (Or.inr le_rfl))
  obtain ⟨f0, _, _⟩ := fv_props P hp ha γ c y P.a hγ hFa
  unfold expProfit
  rw [e1, e2, revInt_ge P q hqa.le ha.le, revInt_ge P P.a le_rfl ha.le]
  have : γ * faceValue P γ c y P.a ^ 2 / (2 * P.a * P.p)
      ≤ γ * faceValue P γ c y q ^ 2 / (2 * P.a * P.p) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hγ
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hqa hc]

lemma mce_ii (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y q : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 < c) (hq : 0 ≤ q) (hy : 0 ≤ y)
    (hcase : c * q ≤ y ∨ 2 * (1 + γ) * (c * q - y) < P.a * P.p) :
    IntervalIntegrable (fun x => mce P γ c y x) MeasureTheory.volume 0 q := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  by_cases hcq : c * q ≤ y
  · have e : Set.EqOn (fun x => mce P γ c y x) (fun _ => (0:ℝ)) (Set.uIcc 0 q) := by
      intro x hx
      rw [Set.uIcc_of_le hq] at hx
      have : c * x ≤ y := by nlinarith [hx.2]
      simp [mce, fv_zero P γ c y x this]
    exact (continuousOn_const.congr e).intervalIntegrable
  have hlend : 2 * (1 + γ) * (c * q - y) < P.a * P.p := hcase.resolve_left hcq
  push_neg at hcq
  set s := y / c with hs
  have hs0 : 0 ≤ s := div_nonneg hy hc.le
  have hcs : c * s = y := by rw [hs]; field_simp
  have hsq : s < q := by
    by_contra h; push_neg at h; nlinarith
  have hupos : ∀ x, x ≤ q → 0 < 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p) := by
    intro x hx
    have : 2 * (1 + γ) * (c * x - y) / (P.a * P.p) < 1 := by
      rw [div_lt_one hap]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right (mul_le_mul_of_nonneg_left hx hc.le) y)
        (by linarith : (0:ℝ) ≤ 2 * (1 + γ))
      linarith
    linarith
  have hden : ∀ x, P.a * P.p - (1 + γ) * Fg P γ c y x
        = P.a * P.p * Real.sqrt (1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p)) := by
    intro x; unfold Fg; field_simp; ring
  have hdenpos : ∀ x, x ≤ q → 0 < P.a * P.p - (1 + γ) * Fg P γ c y x := by
    intro x hx; rw [hden x]
    exact mul_pos hap (Real.sqrt_pos.mpr (hupos x hx))
  set g : ℝ → ℝ := fun x => γ * c * Fg P γ c y x / (P.a * P.p - (1 + γ) * Fg P γ c y x) with hg
  have hgc : ContinuousOn g (Set.Icc s q) := by
    apply ContinuousOn.div
    · exact (continuous_const.mul (Fg_cont P γ c y)).continuousOn
    · exact (continuous_const.sub (continuous_const.mul (Fg_cont P γ c y))).continuousOn
    · intro x hx; exact (hdenpos x hx.2).ne'
  have e2 : Set.EqOn (fun x => mce P γ c y x) g (Set.uIcc s q) := by
    intro x hx
    rw [Set.uIcc_of_le hsq.le] at hx
    have : y ≤ c * x := by rw [← hcs]; nlinarith [hx.1]
    simp only [mce, hg, fv_eq P γ c y x this]
  have e1 : Set.EqOn (fun x => mce P γ c y x) (fun _ => (0:ℝ)) (Set.uIcc 0 s) := by
    intro x hx
    rw [Set.uIcc_of_le hs0] at hx
    have : c * x ≤ y := by rw [← hcs]; nlinarith [hx.2]
    simp [mce, fv_zero P γ c y x this]
  have hi1 : IntervalIntegrable (fun x => mce P γ c y x) MeasureTheory.volume 0 s :=
    (continuousOn_const.congr e1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => mce P γ c y x) MeasureTheory.volume s q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hsq.le] at e2 ⊢
    exact hgc.congr e2
  exact hi1.trans hi2

/-- MCE as `max(G, 0)` wherever the loan bound holds. -/
lemma mceM (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y t : ℝ) (hγ : 0 ≤ γ) (hc : 0 < c)
    (h : c * t ≤ y ∨ 2 * (1 + γ) * (c * t - y) < P.a * P.p) :
    mce P γ c y t = max (γ * c / (1 + γ) *
      ((Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)))⁻¹ - 1)) 0 := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hk : 0 ≤ γ * c / (1 + γ) := div_nonneg (mul_nonneg hγ hc.le) (by linarith)
  by_cases h' : c * t ≤ y
  · have hu : 1 ≤ 1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p) := by
      have : 2 * (1 + γ) * (c * t - y) / (P.a * P.p) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith) hap.le
      linarith
    have h1 : 1 ≤ Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)) := by
      rw [Real.one_le_sqrt]; exact hu
    have : (Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ h1
    rw [max_eq_right (by nlinarith)]
    simp [mce, fv_zero P γ c y t h']
  · push_neg at h'
    have hl := h.resolve_left (not_le.mpr h')
    have u0 : 0 < 1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p) := by
      have : 2 * (1 + γ) * (c * t - y) / (P.a * P.p) < 1 := by rw [div_lt_one hap]; exact hl
      linarith
    have u1 : 1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p) ≤ 1 := by
      have : 0 ≤ 2 * (1 + γ) * (c * t - y) / (P.a * P.p) := div_nonneg (by nlinarith) hap.le
      linarith
    have hs : Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact u1
    have hs0 := Real.sqrt_pos.mpr u0
    have hi : 1 ≤ (Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)))⁻¹ :=
      (one_le_inv₀ hs0).mpr hs
    simp only [mce, fv_eq P γ c y t h'.le]
    rw [g_eq P hp ha γ c y t hγ u0]
    rw [max_eq_left (by nlinarith)]

lemma G_mono (P : Params) (hp : 0 < P.p) (ha : 0 < P.a) (γ c y t v : ℝ) (hγ : 0 ≤ γ) (hc : 0 < c)
    (htv : t ≤ v) (hv : 0 < 1 - 2 * (1 + γ) * (c * v - y) / (P.a * P.p)) :
    γ * c / (1 + γ) * ((Real.sqrt (1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p)))⁻¹ - 1)
      ≤ γ * c / (1 + γ) * ((Real.sqrt (1 - 2 * (1 + γ) * (c * v - y) / (P.a * P.p)))⁻¹ - 1) := by
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hk : 0 ≤ γ * c / (1 + γ) := div_nonneg (mul_nonneg hγ hc.le) (by linarith)
  apply mul_le_mul_of_nonneg_left _ hk
  have hle : 1 - 2 * (1 + γ) * (c * v - y) / (P.a * P.p)
      ≤ 1 - 2 * (1 + γ) * (c * t - y) / (P.a * P.p) := by
    have : 2 * (1 + γ) * (c * t - y) ≤ 2 * (1 + γ) * (c * v - y) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left htv hc.le]) (by linarith)
    have := div_le_div_of_nonneg_right this hap.le
    linarith
  have hs := Real.sqrt_le_sqrt hle
  have hs0 := Real.sqrt_pos.mpr hv
  have := inv_anti₀ hs0 hs
  linarith

lemma recInt (P : Params) (hp : 0 < P.p) (γ q F : ℝ) (hq : 0 ≤ q) (hF0 : 0 ≤ F)
    (hFa : F ≤ P.a * P.p) (hFq : F < P.p * q) :
    ∫ ξ in (0)..P.a, (min (revenue P q ξ) F - γ * revenue P q ξ *
      (if revenue P q ξ ≤ F then 1 else 0))
      = (1 - γ) * P.p * (F / P.p) ^ 2 / 2 + F * (P.a - F / P.p) := by
  set f : ℝ → ℝ := fun ξ => min (revenue P q ξ) F - γ * revenue P q ξ *
      (if revenue P q ξ ≤ F then (1:ℝ) else 0) with hf
  set b := F / P.p with hb
  have hb0 : 0 ≤ b := div_nonneg hF0 hp.le
  have hba : b ≤ P.a := by rw [hb, div_le_iff₀ hp]; linarith
  have hbq : b < q := by rw [hb, div_lt_iff₀ hp]; linarith
  have e1 : ∀ x ∈ Set.Ioc 0 b, f x = (1 - γ) * P.p * x := by
    intro x hx
    have hxq : x ≤ q := by linarith [hx.2]
    have hle : P.p * x ≤ F := by
      have := hx.2; rw [hb, le_div_iff₀ hp] at this; linarith
    have hr : revenue P q x = P.p * x := by simp [revenue, min_eq_right hxq]
    simp only [hf]; rw [hr, if_pos hle, min_eq_left hle]; ring
  have e2 : ∀ x ∈ Set.Ioc b P.a, f x = F := by
    intro x hx
    have hgt : F < P.p * x := by
      have := hx.1; rw [hb, div_lt_iff₀ hp] at this; linarith
    have hr : F < revenue P q x := by
      unfold revenue
      rcases le_or_gt x q with hxq | hxq
      · rw [min_eq_right hxq]; exact hgt
      · rw [min_eq_left hxq.le]; exact hFq
    simp only [hf]; rw [if_neg (not_le.mpr hr), min_eq_right hr.le]; ring
  have hi1 : IntervalIntegrable f MeasureTheory.volume 0 b := by
    have hc : Continuous (fun x : ℝ => (1 - γ) * P.p * x) := by fun_prop
    apply (hc.intervalIntegrable 0 b).congr
    rw [Set.uIoc_of_le hb0]
    intro x hx; exact (e1 x hx).symm
  have hi2 : IntervalIntegrable f MeasureTheory.volume b P.a := by
    apply (intervalIntegrable_const (c := F)).congr
    rw [Set.uIoc_of_le hba]
    intro x hx; exact (e2 x hx).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have j1 : ∫ x in (0)..b, f x = ∫ x in (0)..b, (1 - γ) * P.p * x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hb0] at hx
    exact e1 x hx
  have j2 : ∫ x in b..P.a, f x = ∫ x in b..P.a, F := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hba] at hx
    exact e2 x hx
  rw [j1, j2, intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp; ring

end FIP4P1

open FIP4Help FIP4L1 FIP4P1 in
theorem solution (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y)
    (hfeas : Feasible P γ c y q) (hborrow : y < c * q) :
    (IsEqQuantity P γ c y q ↔ mrr P c q = mce P γ c y q) ∧
    bankReceipt P γ q (faceValue P γ c y q) = c * q - y := by
  have hγ0 : 0 ≤ γ := hγ.1
  have hap : 0 < P.a * P.p := mul_pos ha hp
  have hl := hfeas.2.resolve_left (not_le.mpr hborrow)
  have hq := hfeas.1
  obtain ⟨F0, F1, _⟩ := fv_props P hp ha γ c y q hγ0 hfeas
  have hFq : faceValue P γ c y q < P.p * q := by linarith [hl.2]
  have hu0 : 0 < 1 - 2 * (1 + γ) * (c * q - y) / (P.a * P.p) := by
    have : 2 * (1 + γ) * (c * q - y) / (P.a * P.p) < 1 := by rw [div_lt_one hap]; exact hl.1
    linarith
  constructor
  swap
  · -- loan pricing
    unfold bankReceipt
    rw [recInt P hp γ q _ hq F0 F1 hFq, fv_eq P γ c y q hborrow.le]
    set F := Fg P γ c y q with hFdef
    have h1 : 1 / P.a * ((1 - γ) * P.p * (F / P.p) ^ 2 / 2 + F * (P.a - F / P.p))
        = F - (1 + γ) * F ^ 2 / (2 * P.a * P.p) := by
      field_simp; ring
    rw [h1]
    have hr2 := Real.sq_sqrt hu0.le
    set r := Real.sqrt (1 - 2 * (1 + γ) * (c * q - y) / (P.a * P.p)) with hr
    have hF' : F = P.a * P.p / (1 + γ) * (1 - r) := by rw [hFdef]; unfold Fg; rw [← hr]
    have h1g : (1 + γ) ≠ 0 := by linarith
    have h2 : F - (1 + γ) * F ^ 2 / (2 * P.a * P.p) = P.a * P.p / (1 + γ) * (1 - r ^ 2) / 2 := by
      rw [hF']; field_simp; ring
    rw [h2, hr2]
    field_simp; ring
  -- the equilibrium characterization
  have condF : ∀ v, Feasible P γ c y v → (c * v ≤ y ∨ 2 * (1 + γ) * (c * v - y) < P.a * P.p) := by
    intro v hv
    rcases hv.2 with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  have condDown : ∀ t v, t ≤ v → (c * v ≤ y ∨ 2 * (1 + γ) * (c * v - y) < P.a * P.p) →
      (c * t ≤ y ∨ 2 * (1 + γ) * (c * t - y) < P.a * P.p) := by
    intro t v htv h
    have hct : c * t ≤ c * v := mul_le_mul_of_nonneg_left htv hc.le
    rcases h with h | h
    · exact Or.inl (le_trans hct h)
    · right
      have : 2 * (1 + γ) * (c * t - y) ≤ 2 * (1 + γ) * (c * v - y) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
  have condU : ∀ v, (c * v ≤ y ∨ 2 * (1 + γ) * (c * v - y) < P.a * P.p) →
      0 < 1 - 2 * (1 + γ) * (c * v - y) / (P.a * P.p) := by
    intro v h
    rcases h with h | h
    · have : 2 * (1 + γ) * (c * v - y) / (P.a * P.p) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith) hap.le
      linarith
    · have : 2 * (1 + γ) * (c * v - y) / (P.a * P.p) < 1 := by rw [div_lt_one hap]; exact h
      linarith
  have mceMono : ∀ t v, t ≤ v → (c * v ≤ y ∨ 2 * (1 + γ) * (c * v - y) < P.a * P.p) →
      mce P γ c y t ≤ mce P γ c y v := by
    intro t v htv h
    rw [mceM P hp ha γ c y t hγ0 hc (condDown t v htv h), mceM P hp ha γ c y v hγ0 hc h]
    exact max_le_max (G_mono P hp ha γ c y t v hγ0 hc htv (condU v h)) le_rfl
  constructor
  · intro heq
    have hqa := eq_le_a P hp ha γ c y q hγ0 hc heq
    set E : ℝ → ℝ := fun x => P.p * x - P.p * x ^ 2 / (2 * P.a) - c * x
      - γ * Fg P γ c y x ^ 2 / (2 * P.a * P.p) with hE
    have hΦ := (((hasDerivAt_id q).const_mul P.p).sub
      (((hasDerivAt_id q).pow 2).const_mul P.p |>.div_const (2 * P.a))).sub
      ((hasDerivAt_id q).const_mul c)
    have hH := H_deriv P hp ha γ c y q hγ0 hu0
    have hEd : HasDerivAt E _ q := hΦ.sub hH
    set U : Set ℝ := {x | y < c * x ∧ 2 * (1 + γ) * (c * x - y) < P.a * P.p ∧
        Fg P γ c y x < x * P.p} with hU
    have hUo : IsOpen U := by
      have hFc := Fg_cont P γ c y
      simp only [hU, Set.setOf_and]
      apply IsOpen.inter (isOpen_lt continuous_const (by fun_prop))
      apply IsOpen.inter (isOpen_lt (by fun_prop) continuous_const)
      exact isOpen_lt hFc (by fun_prop)
    have hqU : q ∈ U := ⟨hborrow, hl.1, by rw [← fv_eq P γ c y q hborrow.le]; exact hl.2⟩
    have hmax : IsLocalMax E q := by
      filter_upwards [hUo.mem_nhds hqU] with x hx
      have hx0 : 0 ≤ x := by
        by_contra h; push_neg at h; nlinarith [hx.1]
      have hfx : Feasible P γ c y x := ⟨hx0, Or.inr ⟨hx.2.1, by
        rw [fv_eq P γ c y x hx.1.le]; exact hx.2.2⟩⟩
      have hbx := bankCost_eq P hp ha γ c y x hγ0 hfx (Or.inr (Or.inl (by
        rw [fv_eq P γ c y x hx.1.le]; linarith [hx.2.2])))
      rw [fv_eq P γ c y x hx.1.le] at hbx
      have hbq := bankCost_eq P hp ha γ c y q hγ0 hfeas (Or.inr (Or.inl hFq))
      rw [fv_eq P γ c y q hborrow.le] at hbq
      have hle := heq.2 x hfx
      unfold expProfit at hle
      rw [hbx, hbq, revInt_le P q hq hqa] at hle
      have hR : P.p * x - P.p * x ^ 2 / (2 * P.a)
          ≤ 1 / P.a * ∫ ξ in (0)..P.a, revenue P x ξ := by
        rcases le_total x P.a with hxa | hxa
        · rw [revInt_le P x hx0 hxa]; field_simp; ring_nf; rfl
        · rw [revInt_ge P x hxa ha.le]
          have : 0 ≤ P.p / (2 * P.a) * (x - P.a) ^ 2 := by positivity
          have e : P.p * x - P.p * x ^ 2 / (2 * P.a)
              = 1 / P.a * (P.p * P.a ^ 2 / 2) - P.p / (2 * P.a) * (x - P.a) ^ 2 := by
            field_simp; ring
          linarith
      have e2 : 1 / P.a * (P.p * q ^ 2 / 2 + P.p * q * (P.a - q))
          = P.p * q - P.p * q ^ 2 / (2 * P.a) := by field_simp; ring
      simp only [hE]
      linarith
    have hz := hmax.hasDerivAt_eq_zero hEd
    unfold mrr
    simp only [mce, fv_eq P γ c y q hborrow.le]
    have : P.a ≠ 0 := ha.ne'
    field_simp at hz ⊢
    norm_num at hz
    have e : 2 * P.a * c * γ * Fg P γ c y q / (P.p * P.a - Fg P γ c y q * (1 + γ))
        = 2 * (P.a * c * γ * Fg P γ c y q / (P.p * P.a - Fg P γ c y q * (1 + γ))) := by ring
    rw [e] at hz
    linarith
  · intro hmc
    have hmce0 : 0 ≤ mce P γ c y q := by
      rw [mceM P hp ha γ c y q hγ0 hc (condF q hfeas)]; exact le_max_right _ _
    have hqa : q ≤ P.a := by
      have : 0 ≤ mrr P c q := hmc ▸ hmce0
      unfold mrr at this
      by_contra h; push_neg at h
      have : q / P.a > 1 := by rw [gt_iff_lt, one_lt_div ha]; exact h
      nlinarith
    have key : ∀ x, Feasible P γ c y x → x ≤ P.a → expProfit P γ c y x ≤ expProfit P γ c y q := by
      intro x hx hxa
      rw [profit_eq P hp ha γ c y x hγ0 hc hy hx hxa, profit_eq P hp ha γ c y q hγ0 hc hy hfeas hqa]
      have iq := mce_ii P hp ha γ c y q hγ0 hc hq hy (condF q hfeas)
      have ix := mce_ii P hp ha γ c y x hγ0 hc hx.1 hy (condF x hx)
      have hsub := intervalIntegral.integral_interval_sub_left iq ix
      have hmrrI : ∀ u v : ℝ, IntervalIntegrable (fun t => mrr P c t) MeasureTheory.volume u v := by
        intro u v; apply Continuous.intervalIntegrable; unfold mrr; fun_prop
      have hxq := intervalIntegral.integral_sub (hmrrI x q) (ix.symm.trans iq)
      rw [mrrInt P ha] at hxq
      rcases le_total x q with h | h
      · have hnn : 0 ≤ ∫ t in x..q, (mrr P c t - mce P γ c y t) := by
          apply intervalIntegral.integral_nonneg h
          intro t ht
          have h1 := mceMono t q ht.2 (condF q hfeas)
          have h2 : mrr P c q ≤ mrr P c t := by
            unfold mrr
            have : t / P.a ≤ q / P.a := div_le_div_of_nonneg_right ht.2 ha.le
            nlinarith
          linarith
        linarith
      · have hnn : 0 ≤ ∫ t in q..x, (mce P γ c y t - mrr P c t) := by
          apply intervalIntegral.integral_nonneg h
          intro t ht
          have h1 := mceMono q t ht.1 (condDown t x ht.2 (condF x hx))
          have h2 : mrr P c t ≤ mrr P c q := by
            unfold mrr
            have : q / P.a ≤ t / P.a := div_le_div_of_nonneg_right ht.1 ha.le
            nlinarith
          linarith
        have hsw : ∫ t in q..x, (mce P γ c y t - mrr P c t)
            = ∫ t in x..q, (mrr P c t - mce P γ c y t) := by
          have hs := intervalIntegral.integral_symm (μ := MeasureTheory.volume)
            (f := fun t => mce P γ c y t - mrr P c t) x q
          rw [hs, ← intervalIntegral.integral_neg]
          congr 1; funext t; ring
        linarith
    refine ⟨hfeas, fun x hx => ?_⟩
    rcases le_or_gt x P.a with hxa | hxa
    · exact key x hx hxa
    · obtain ⟨hfa, hlt⟩ := beyond_a P hp ha γ c y x hγ0 hc hx hxa
      linarith [key P.a hfa le_rfl]

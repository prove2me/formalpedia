-- Prove2me | solution 1 for FrictionInvest.Benefit.proposition_3_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:04:51.605421+00:00
-- url     : https://prove2.me/submissions/461d3b85-607a-4d30-b98c-0fe6c6c7c041

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

open FIP4Help in
theorem solution (P : Params) (hS : P.Standing)
    (hcp : P.c1 < P.p) (γ : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1)
    (q0 qA : ℝ) (h0 : IsEqQuantity P γ P.c1 P.y1 q0)
    (hA : IsEqQuantity P γ P.c2 P.y2 qA)
    (q0' qA' : ℝ) (h0' : IsEqQuantity P 0 P.c1 P.y1 q0')
    (hA' : IsEqQuantity P 0 P.c2 P.y2 qA') :
    netBenefit P γ q0 qA =
      opEffect P q0' qA' + frictionEffect P γ q0 qA - P.A := by
  obtain ⟨hp, ha, hc1, hAp, hβ, hc2, hAy⟩ := hS
  have hy1 : 0 ≤ P.y1 := by linarith
  have hy2 : 0 ≤ P.y2 := by unfold Params.y2; linarith
  have hc21 : P.c2 < P.c1 := by unfold Params.c2; nlinarith
  have hγ0 : 0 ≤ γ := hγ.1
  have e0 := profit_eq P hp ha γ P.c1 P.y1 q0 hγ0 hc1 hy1 h0.1 (eq_le_a P hp ha γ _ _ q0 hγ0 hc1 h0)
  have eA := profit_eq P hp ha γ P.c2 P.y2 qA hγ0 hc2 hy2 hA.1 (eq_le_a P hp ha γ _ _ qA hγ0 hc2 hA)
  have p0 := perfect P hp ha P.c1 P.y1 q0' hc1 hcp hy1 h0'
  have pA := perfect P hp ha P.c2 P.y2 qA' hc2 (by linarith) hy2 hA'
  unfold frictionEffect opEffect netBenefit
  rw [mrrInt P ha, mrrInt P ha, e0, eA, p0, pA]
  have k1 : P.p * (P.a * (P.p - P.c1) / P.p) - P.p * (P.a * (P.p - P.c1) / P.p) ^ 2 / (2 * P.a)
      - P.c1 * (P.a * (P.p - P.c1) / P.p) = P.a * (P.p - P.c1) ^ 2 / (2 * P.p) := by
    field_simp; ring
  have k2 : P.p * (P.a * (P.p - P.c2) / P.p) - P.p * (P.a * (P.p - P.c2) / P.p) ^ 2 / (2 * P.a)
      - P.c2 * (P.a * (P.p - P.c2) / P.p) = P.a * (P.p - P.c2) ^ 2 / (2 * P.p) := by
    field_simp; ring
  rw [k1, k2]
  ring

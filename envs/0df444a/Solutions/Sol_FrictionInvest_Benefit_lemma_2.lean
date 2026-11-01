-- Prove2me | solution 1 for FrictionInvest.Benefit.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:10:41.898265+00:00
-- url     : https://prove2.me/submissions/0d457f36-e12e-4199-b3f8-6f37c448569f

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

namespace FIP4L2

lemma sqrt_conc (u1 u2 a b : ℝ) (h1 : 0 ≤ u1) (h2 : 0 ≤ u2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * Real.sqrt u1 + b * Real.sqrt u2 ≤ Real.sqrt (a * u1 + b * u2) := by
  have s1 := Real.sqrt_nonneg u1
  have s2 := Real.sqrt_nonneg u2
  apply Real.le_sqrt_of_sq_le
  have e1 := Real.sq_sqrt h1
  have e2 := Real.sq_sqrt h2
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, sq_nonneg (Real.sqrt u1 - Real.sqrt u2),
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (Real.sqrt u1 - Real.sqrt u2))]

lemma invsqrt_conv (u1 u2 a b : ℝ) (h1 : 0 < u1) (h2 : 0 < u2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    (Real.sqrt (a * u1 + b * u2))⁻¹ ≤ a * (Real.sqrt u1)⁻¹ + b * (Real.sqrt u2)⁻¹ := by
  have s1 := Real.sqrt_pos.mpr h1
  have s2 := Real.sqrt_pos.mpr h2
  set r1 := Real.sqrt u1
  set r2 := Real.sqrt u2
  have hm : 0 < a * r1 + b * r2 := by
    rcases eq_or_lt_of_le ha with h | h
    · subst h; have : b = 1 := by linarith
      subst this; linarith
    · nlinarith [mul_pos h s1, mul_nonneg hb s2.le]
  have hle := sqrt_conc u1 u2 a b h1.le h2.le ha hb hab
  calc (Real.sqrt (a * u1 + b * u2))⁻¹ ≤ (a * r1 + b * r2)⁻¹ := inv_anti₀ hm hle
    _ ≤ a * r1⁻¹ + b * r2⁻¹ := by
      rw [inv_le_iff_one_le_mul₀' hm]
      have hb' : b = 1 - a := by linarith
      subst hb'
      have key : (a * r1 + (1 - a) * r2) * (a * r1⁻¹ + (1 - a) * r2⁻¹)
          = 1 + a * (1 - a) * (r1 - r2) ^ 2 / (r1 * r2) := by
        field_simp; ring
      rw [key]
      have : 0 ≤ a * (1 - a) * (r1 - r2) ^ 2 / (r1 * r2) := by
        apply div_nonneg _ (mul_pos s1 s2).le
        exact mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
      linarith

end FIP4L2

open FIP4Help FIP4L1 FIP4L2 in
theorem solution (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y : ℝ) (hγ : 0 < γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y) :
    ConvexOn ℝ {q : ℝ | Feasible P γ c y q} (mce P γ c y) ∧
    StrictMonoOn (mce P γ c y) {q : ℝ | Feasible P γ c y q ∧ y < c * q} ∧
    MonotoneOn (mce P γ c y) {q : ℝ | Feasible P γ c y q} := by
  have hγ0 : 0 ≤ γ := hγ.1.le
  have hap : 0 < P.a * P.p := mul_pos ha hp
  set u : ℝ → ℝ := fun x => 1 - 2 * (1 + γ) * (c * x - y) / (P.a * P.p) with hu_def
  set k := γ * c / (1 + γ) with hk
  have hk0 : 0 < k := div_pos (mul_pos hγ.1 hc) (by linarith)
  set G : ℝ → ℝ := fun x => k * ((Real.sqrt (u x))⁻¹ - 1) with hG
  set M : ℝ → ℝ := fun x => max (G x) 0 with hM
  set S := {q : ℝ | Feasible P γ c y q} with hS
  have hK0 : 0 < P.a * P.p / (1 + γ) := div_pos hap (by linarith)
  -- facts about self-financed points
  have self_u : ∀ x, c * x ≤ y → 1 ≤ u x := by
    intro x hx
    have : 2 * (1 + γ) * (c * x - y) / (P.a * P.p) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hap.le
    simp only [hu_def]; linarith
  have lend_u : ∀ x, y < c * x → 2 * (1 + γ) * (c * x - y) < P.a * P.p → 0 < u x ∧ u x < 1 := by
    intro x h1 h2
    have a1 : 0 < 2 * (1 + γ) * (c * x - y) / (P.a * P.p) := div_pos (by nlinarith) hap
    have a2 : 2 * (1 + γ) * (c * x - y) / (P.a * P.p) < 1 := by rw [div_lt_one hap]; exact h2
    simp only [hu_def]; constructor <;> linarith
  have hupos : ∀ x ∈ S, 0 < u x := by
    intro x hx
    rcases hx.2 with h | h
    · linarith [self_u x h]
    · by_cases h' : c * x ≤ y
      · linarith [self_u x h']
      · exact (lend_u x (by push_neg at h'; exact h') h.1).1
  have Fg_self : ∀ x, c * x ≤ y → Fg P γ c y x ≤ 0 := by
    intro x hx
    have : 1 ≤ Real.sqrt (u x) := by rw [Real.one_le_sqrt]; exact self_u x hx
    unfold Fg; simp only [hu_def] at this
    nlinarith
  have hEq : ∀ x ∈ S, mce P γ c y x = M x := by
    intro x hx
    by_cases h' : c * x ≤ y
    · have h1 : 1 ≤ Real.sqrt (u x) := by rw [Real.one_le_sqrt]; exact self_u x h'
      have : G x ≤ 0 := by
        simp only [hG]
        have : (Real.sqrt (u x))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        nlinarith
      simp only [hM, max_eq_right this, mce, fv_zero P γ c y x h']; simp
    · push_neg at h'
      have hl := (hx.2.resolve_left (not_le.mpr h')).1
      obtain ⟨u0, u1⟩ := lend_u x h' hl
      have hs : Real.sqrt (u x) < 1 := by
        rw [Real.sqrt_lt' one_pos]; simpa using u1
      have hs0 := Real.sqrt_pos.mpr u0
      have : 0 < G x := by
        simp only [hG]
        have : 1 < (Real.sqrt (u x))⁻¹ := (one_lt_inv₀ hs0).mpr hs
        nlinarith
      simp only [hM, max_eq_left this.le, mce, fv_eq P γ c y x h'.le]
      rw [g_eq P hp ha γ c y x hγ0 u0]
  have hu_aff : ∀ x w a b : ℝ, a + b = 1 → u (a * x + b * w) = a * u x + b * u w := by
    intro x w a b hab
    simp only [hu_def]
    have hb : b = 1 - a := by linarith
    subst hb; field_simp; ring
  -- convexity of S
  have hSc : Convex ℝ S := by
    intro x hx w hw a b ha hb hab
    simp only [smul_eq_mul]
    have hz0 : 0 ≤ a * x + b * w := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hw.1)
    refine ⟨hz0, ?_⟩
    by_cases hz : c * (a * x + b * w) ≤ y
    · exact Or.inl hz
    right
    push_neg at hz
    have bx : ∀ v ∈ S, 2 * (1 + γ) * (c * v - y) < P.a * P.p := by
      intro v hv
      rcases hv.2 with h | h
      · nlinarith
      · exact h.1
    have hbd : 2 * (1 + γ) * (c * (a * x + b * w) - y)
        = a * (2 * (1 + γ) * (c * x - y)) + b * (2 * (1 + γ) * (c * w - y)) := by
      have hb' : b = 1 - a := by linarith
      subst hb'; ring
    refine ⟨?_, ?_⟩
    · rw [hbd]
      have hX := bx x hx; have hY := bx w hw
      have hb' : b = 1 - a := by linarith
      subst hb'
      rcases eq_or_lt_of_le ha with h0 | h0
      · subst h0; linarith
      · nlinarith [mul_lt_mul_of_pos_left hX h0, mul_le_mul_of_nonneg_left hY.le hb]
    · rw [fv_eq P γ c y _ hz.le]
      have hFc : Fg P γ c y (a * x + b * w) ≤ a * Fg P γ c y x + b * Fg P γ c y w := by
        have hsc := sqrt_conc (u x) (u w) a b (hupos x hx).le (hupos w hw).le ha hb hab
        rw [← hu_aff x w a b hab] at hsc
        unfold Fg
        simp only [hu_def] at hsc
        have hb' : b = 1 - a := by linarith
        subst hb'
        nlinarith
      -- slack at each point
      have dx : ∀ v ∈ S, Fg P γ c y v ≤ v * P.p ∧ (y < c * v → Fg P γ c y v < v * P.p) := by
        intro v hv
        by_cases h' : c * v ≤ y
        · have := Fg_self v h'
          exact ⟨by nlinarith [hv.1], fun h => absurd h (not_lt.mpr h')⟩
        · push_neg at h'
          have h2 := (hv.2.resolve_left (not_le.mpr h')).2
          rw [fv_eq P γ c y v h'.le] at h2
          exact ⟨h2.le, fun _ => h2⟩
      obtain ⟨x1, x2⟩ := dx x hx
      obtain ⟨w1, w2⟩ := dx w hw
      have hb' : b = 1 - a := by linarith
      subst hb'
      have pos_comb : ∀ dX dW : ℝ, 0 ≤ dX → 0 ≤ dW → ((0 < a ∧ 0 < dX) ∨ (0 < 1 - a ∧ 0 < dW)) →
          0 < a * dX + (1 - a) * dW := by
        intro dX dW h1 h2 h3
        rcases h3 with ⟨p1, p2⟩ | ⟨p1, p2⟩
        · have := mul_pos p1 p2; have := mul_nonneg hb h2; linarith
        · have := mul_pos p1 p2; have := mul_nonneg ha h1; linarith
      have key : 0 < a * (x * P.p - Fg P γ c y x) + (1 - a) * (w * P.p - Fg P γ c y w) := by
        apply pos_comb _ _ (by linarith) (by linarith)
        by_cases hxl : y < c * x
        · rcases eq_or_lt_of_le ha with h0 | h0
          · right
            subst h0
            refine ⟨by norm_num, ?_⟩
            have hwl : y < c * w := by simpa using hz
            linarith [w2 hwl]
          · left; exact ⟨h0, by linarith [x2 hxl]⟩
        · push_neg at hxl
          have hwl : y < c * w := by
            by_contra h0; push_neg at h0
            have e : c * (a * x + (1 - a) * w) = a * (c * x) + (1 - a) * (c * w) := by ring
            nlinarith [mul_le_mul_of_nonneg_left hxl ha, mul_le_mul_of_nonneg_left h0 hb]
          right
          refine ⟨?_, by linarith [w2 hwl]⟩
          by_contra h0; push_neg at h0
          have ha1 : a = 1 := by linarith
          subst ha1
          simp at hz; linarith
      have e : (a * x + (1 - a) * w) * P.p - (a * Fg P γ c y x + (1 - a) * Fg P γ c y w)
          = a * (x * P.p - Fg P γ c y x) + (1 - a) * (w * P.p - Fg P γ c y w) := by ring
      linarith
  -- convexity of M on S
  have hMc : ConvexOn ℝ S M := by
    refine ⟨hSc, ?_⟩
    intro x hx w hw a b ha hb hab
    simp only [smul_eq_mul, hM]
    have hi := invsqrt_conv (u x) (u w) a b (hupos x hx) (hupos w hw) ha hb hab
    rw [← hu_aff x w a b hab] at hi
    have hGz : G (a * x + b * w) ≤ a * G x + b * G w := by
      simp only [hG]
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith
    apply max_le
    · have := le_max_left (G x) 0
      have := le_max_left (G w) 0
      nlinarith
    · have := le_max_right (G x) 0
      have := le_max_right (G w) 0
      nlinarith
  have hGmono : ∀ x w, x < w → 0 < u w → G x < G w := by
    intro x w hxw huw
    have hlt : u w < u x := by
      simp only [hu_def]
      have : 2 * (1 + γ) * (c * x - y) < 2 * (1 + γ) * (c * w - y) :=
        mul_lt_mul_of_pos_left (by nlinarith [mul_lt_mul_of_pos_left hxw hc]) (by linarith)
      have := div_lt_div_of_pos_right this hap
      linarith
    have hs : Real.sqrt (u w) < Real.sqrt (u x) := Real.sqrt_lt_sqrt huw.le hlt
    have hi : (Real.sqrt (u x))⁻¹ < (Real.sqrt (u w))⁻¹ :=
      (inv_lt_inv₀ (lt_trans (Real.sqrt_pos.mpr huw) hs) (Real.sqrt_pos.mpr huw)).mpr hs
    simp only [hG]
    nlinarith
  have hGpos : ∀ v, v ∈ S → y < c * v → 0 < G v := by
    intro v hv hvl
    have hl := (hv.2.resolve_left (not_le.mpr hvl)).1
    obtain ⟨u0, u1⟩ := lend_u v hvl hl
    have hs : Real.sqrt (u v) < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using u1
    have hs0 := Real.sqrt_pos.mpr u0
    have : 1 < (Real.sqrt (u v))⁻¹ := (one_lt_inv₀ hs0).mpr hs
    simp only [hG]; nlinarith
  refine ⟨hMc.congr (fun x hx => (hEq x hx).symm), ?_, ?_⟩
  · intro x hx w hw hxw
    rw [hEq x hx.1, hEq w hw.1]
    simp only [hM, max_eq_left (hGpos x hx.1 hx.2).le, max_eq_left (hGpos w hw.1 hw.2).le]
    exact hGmono x w hxw (hupos w hw.1)
  · intro x hx w hw hxw
    rw [hEq x hx, hEq w hw]
    simp only [hM]
    apply max_le_max _ le_rfl
    rcases eq_or_lt_of_le hxw with h | h
    · rw [h]
    · exact (hGmono x w h (hupos w hw)).le

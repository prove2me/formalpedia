-- Prove2me | solution 1 for DbarRegularity.lintegral_rpow_le_of_distribution_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:03:54.085514+00:00
-- url     : https://prove2.me/submissions/b3819e85-c073-434b-9f1f-87f1553a8cac

import Theorems.Thm_DbarRegularity_lintegral_Ioi_indicator_rpow
import Mathlib.MeasureTheory.Measure.Prod

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Measurable version of `lintegral_rpow_le_of_distribution_le`. -/
lemma lintegral_rpow_le_of_distribution_le_of_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g h : X → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h)
    {p : ℝ} (hp : 1 < p) (C : ℝ≥0∞)
    (H : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < g x} ≤
      C / ENNReal.ofReal t * ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤ 2 ^ (p - 1) * C * ENNReal.ofReal (p / (p - 1)) * ∫⁻ x, h x ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (p * t ^ (p - 1))
  set G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((p - 1) * t ^ (p - 1 - 1))
  set c := ENNReal.ofReal (p / (p - 1))
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := by fun_prop
  have hS : ∀ (b : X → ℝ≥0∞), Measurable b →
      MeasurableSet {z : X × ℝ | ENNReal.ofReal z.2 < b z.1} := fun b hb =>
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hb.comp measurable_fst)
  -- step 1: layer-cake for `g`
  have step1 : ∫⁻ x, g x ^ p ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), F t * μ {x | ENNReal.ofReal t < g x} := by
    calc ∫⁻ x, g x ^ p ∂μ
        = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < g x}.indicator F t) ∂μ := by
          congr 1; ext x; exact (lintegral_Ioi_indicator_rpow (g x) hp0).symm
      _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, {t : ℝ | ENNReal.ofReal t < g x}.indicator F t ∂μ := by
          refine lintegral_lintegral_swap ?_
          refine Measurable.aemeasurable ?_
          exact (hF.comp measurable_snd).indicator (hS g hg)
      _ = _ := by
          congr 1; ext t
          have hm : MeasurableSet {x | ENNReal.ofReal t < g x} := measurableSet_lt measurable_const hg
          rw [← lintegral_indicator_const hm (F t)]
          rfl
  -- step 3: the inner integral in `t`
  have inner : ∀ x, ∫⁻ t in Ioi (0 : ℝ),
      {t : ℝ | ENNReal.ofReal t < h x * 2}.indicator (fun t => c * G t) t =
        c * (h x * 2) ^ (p - 1) := by
    intro x
    rw [← lintegral_Ioi_indicator_rpow (h x * 2) hp1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; ext t
    by_cases ht : ENNReal.ofReal t < h x * 2 <;> simp [indicator_apply, ht] <;> rfl
  have hFG : ∀ t : ℝ, 0 < t → F t / ENNReal.ofReal t = c * G t := by
    intro t ht
    rw [← ENNReal.ofReal_div_of_pos ht, ← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le)]
    congr 1
    rw [Real.rpow_sub_one ht.ne' (p - 1)]
    field_simp
  set K : X × ℝ → ℝ≥0∞ := {z : X × ℝ | ENNReal.ofReal z.2 < h z.1 * 2}.indicator
    (fun z => h z.1 * (c * G z.2)) with hKdef
  have hK : Measurable K :=
    ((hh.comp measurable_fst).mul (measurable_const.mul (hG.comp measurable_snd))).indicator
      (hS (fun x => h x * 2) (hh.mul_const 2))
  have step2 : ∀ t : ℝ, 0 < t → F t * (C / ENNReal.ofReal t *
      ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ) = C * ∫⁻ x, K (x, t) ∂μ := by
    intro t ht
    have hI : Measurable ({x | ENNReal.ofReal t / 2 < h x}.indicator h) :=
      hh.indicator (measurableSet_lt measurable_const hh)
    calc F t * (C / ENNReal.ofReal t * ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ)
        = C * ((F t / ENNReal.ofReal t) *
            ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ) := by
          have e : ∀ a b r i : ℝ≥0∞, a * (b / r * i) = b * (a / r * i) := fun a b r i => by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
          exact e _ _ _ _
      _ = C * ∫⁻ x, (c * G t) * {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ := by
          rw [hFG t ht, lintegral_const_mul _ hI]
      _ = C * ∫⁻ x, K (x, t) ∂μ := by
          congr 1
          refine lintegral_congr fun x => ?_
          simp only [hKdef, indicator_apply, mem_setOf_eq]
          have hiff : ENNReal.ofReal t / 2 < h x ↔ ENNReal.ofReal t < h x * 2 :=
            ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)
          by_cases hx : ENNReal.ofReal t < h x * 2
          · rw [if_pos (hiff.2 hx), if_pos hx]; ring
          · rw [if_neg (mt hiff.1 hx), if_neg hx]; ring
  have step4 : ∀ x, ∫⁻ t in Ioi (0 : ℝ), K (x, t) = h x * (c * (h x * 2) ^ (p - 1)) := by
    intro x
    rw [← inner x, ← lintegral_const_mul]
    · refine lintegral_congr fun t => ?_
      simp only [hKdef, indicator_apply, mem_setOf_eq]
      split_ifs <;> simp
    · exact (measurable_const.mul hG).indicator
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  calc ∫⁻ x, g x ^ p ∂μ
      = ∫⁻ t in Ioi (0 : ℝ), F t * μ {x | ENNReal.ofReal t < g x} := step1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), F t * (C / ENNReal.ofReal t *
          ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => mul_le_mul_right (H t ht) _
    _ = ∫⁻ t in Ioi (0 : ℝ), C * ∫⁻ x, K (x, t) ∂μ :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => step2 t ht
    _ = C * ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), K (x, t)) ∂μ := by
        rw [lintegral_const_mul C (f := fun t => ∫⁻ x, K (x, t) ∂μ)
          (hK.comp measurable_swap).lintegral_prod_right']
        congr 1
        exact (lintegral_lintegral_swap (f := fun x t => K (x, t)) hK.aemeasurable).symm
    _ = C * ∫⁻ x, (2 ^ (p - 1) * c) * h x ^ p ∂μ := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [step4 x, ENNReal.mul_rpow_of_nonneg _ _ hp1.le]
        have e : h x ^ p = h x * h x ^ (p - 1) := by
          conv_lhs => rw [show p = 1 + (p - 1) by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one hp1.le, ENNReal.rpow_one]
        rw [e]; ring
    _ = 2 ^ (p - 1) * C * c * ∫⁻ x, h x ^ p ∂μ := by
        rw [lintegral_const_mul _ (hh.pow_const p)]; ring

/-- A distribution bound `μ{g > t} ≤ (C/t) ∫_{h > t/2} h` for all `t > 0` gives
`∫ g^p ≤ 2^(p-1) C p/(p-1) ∫ h^p` for every `p > 1`. -/
theorem lintegral_rpow_le_of_distribution_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) {p : ℝ}
    (hp : 1 < p) (C : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) / 2 < h x}.indicator h x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤ 2 ^ (p - 1) * C * ENNReal.ofReal (p / (p - 1)) * ∫⁻ x, h x ^ p ∂μ := by
  have eg := hg.ae_eq_mk
  have eh := hh.ae_eq_mk
  have hL : ∫⁻ x, g x ^ p ∂μ = ∫⁻ x, hg.mk g x ^ p ∂μ :=
    lintegral_congr_ae (eg.mono fun x hx => by simp only [hx])
  have hR : ∫⁻ x, h x ^ p ∂μ = ∫⁻ x, hh.mk h x ^ p ∂μ :=
    lintegral_congr_ae (eh.mono fun x hx => by simp only [hx])
  rw [hL, hR]
  refine lintegral_rpow_le_of_distribution_le_of_measurable μ hg.measurable_mk hh.measurable_mk
    hp C fun t ht => ?_
  have h1 : μ {x | ENNReal.ofReal t < hg.mk g x} = μ {x | ENNReal.ofReal t < g x} :=
    measure_congr (eg.mono fun x hx => by
      change (ENNReal.ofReal t < hg.mk g x) = (ENNReal.ofReal t < g x)
      rw [hx])
  have h2 : ∫⁻ x, {x | ENNReal.ofReal t / 2 < hh.mk h x}.indicator (hh.mk h) x ∂μ =
      ∫⁻ x, {x | ENNReal.ofReal t / 2 < h x}.indicator h x ∂μ :=
    lintegral_congr_ae (eh.mono fun x hx => by
      simp only [indicator_apply, mem_setOf_eq, hx])
  rw [h1, h2]
  exact H t.toNNReal (Real.toNNReal_pos.2 ht)

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) {p : ℝ}
    (hp : 1 < p) (C : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) / 2 < h x}.indicator h x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤ 2 ^ (p - 1) * C * ENNReal.ofReal (p / (p - 1)) * ∫⁻ x, h x ^ p ∂μ :=
  lintegral_rpow_le_of_distribution_le μ hg hh hp C H

-- Prove2me | solution 1 for DbarRegularity.lintegral_rpow_le_of_distribution_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:55:26.970301+00:00
-- url     : https://prove2.me/submissions/ed0b4378-06b3-4df6-82a5-6d05dd44ee72

import Theorems.Thm_DbarRegularity_lintegral_Ioi_indicator_rpow
import Theorems.Thm_DbarRegularity_lintegral_Ioi_indicator_rpow_neg
import Mathlib.MeasureTheory.Measure.Prod

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Measurable version of `lintegral_rpow_le_of_distribution_le_two`. -/
lemma lintegral_rpow_le_of_distribution_le_two_of_measurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g h : X → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) (C D : ℝ≥0∞)
    (H : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < g x} ≤
      C / ENNReal.ofReal t * ∫⁻ x, {x | ENNReal.ofReal t < h x}.indicator h x ∂μ +
      (D / ENNReal.ofReal t) ^ r *
        ∫⁻ x, {x | h x ≤ ENNReal.ofReal t}.indicator (fun x => h x ^ r) x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤
      (C * ENNReal.ofReal (p / (p - 1)) + D ^ r * ENNReal.ofReal (p / (r - p))) *
        ∫⁻ x, h x ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hrp : 0 < r - p := by linarith
  have hr0 : 0 < r := by linarith
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (p * t ^ (p - 1))
  set G1 : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((p - 1) * t ^ (p - 1 - 1))
  set G2 : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ((r - p) * t ^ (-(r - p) - 1))
  set c1 := ENNReal.ofReal (p / (p - 1))
  set c2 := ENNReal.ofReal (p / (r - p))
  have hF : Measurable F := by fun_prop
  have hG1 : Measurable G1 := by fun_prop
  have hG2 : Measurable G2 := by fun_prop
  have hS : ∀ (b : X → ℝ≥0∞), Measurable b →
      MeasurableSet {z : X × ℝ | ENNReal.ofReal z.2 < b z.1} := fun b hb =>
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hb.comp measurable_fst)
  have hS' : MeasurableSet {z : X × ℝ | h z.1 ≤ ENNReal.ofReal z.2} :=
    measurableSet_le (hh.comp measurable_fst) (ENNReal.measurable_ofReal.comp measurable_snd)
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
  have hFG1 : ∀ t : ℝ, 0 < t → F t / ENNReal.ofReal t = c1 * G1 t := by
    intro t ht
    rw [← ENNReal.ofReal_div_of_pos ht, ← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le)]
    congr 1
    rw [Real.rpow_sub_one ht.ne' (p - 1)]
    field_simp
  have hFG2 : ∀ t : ℝ, 0 < t → F t / ENNReal.ofReal t ^ r = c2 * G2 t := by
    intro t ht
    rw [ENNReal.ofReal_rpow_of_pos ht, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ht r),
      ← ENNReal.ofReal_mul (div_nonneg hp0.le hrp.le)]
    congr 1
    rw [mul_div_assoc, ← Real.rpow_sub ht, show p - 1 - r = -(r - p) - 1 by ring,
      ← mul_assoc, div_mul_cancel₀ _ hrp.ne']
  set K1 : X × ℝ → ℝ≥0∞ := {z : X × ℝ | ENNReal.ofReal z.2 < h z.1}.indicator
    (fun z => h z.1 * (c1 * G1 z.2)) with hK1def
  set K2 : X × ℝ → ℝ≥0∞ := {z : X × ℝ | h z.1 ≤ ENNReal.ofReal z.2}.indicator
    (fun z => h z.1 ^ r * (c2 * G2 z.2)) with hK2def
  have hK1 : Measurable K1 :=
    ((hh.comp measurable_fst).mul (measurable_const.mul (hG1.comp measurable_snd))).indicator
      (hS h hh)
  have hK2 : Measurable K2 :=
    (((hh.comp measurable_fst).pow_const r).mul
      (measurable_const.mul (hG2.comp measurable_snd))).indicator hS'
  have e : ∀ a b u i : ℝ≥0∞, a * (b / u * i) = b * (a / u * i) := fun a b u i => by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  have step2a : ∀ t : ℝ, 0 < t → F t * (C / ENNReal.ofReal t *
      ∫⁻ x, {x | ENNReal.ofReal t < h x}.indicator h x ∂μ) = C * ∫⁻ x, K1 (x, t) ∂μ := by
    intro t ht
    have hI : Measurable ({x | ENNReal.ofReal t < h x}.indicator h) :=
      hh.indicator (measurableSet_lt measurable_const hh)
    rw [e, hFG1 t ht, ← lintegral_const_mul _ hI]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [hK1def, indicator_apply, mem_setOf_eq]
    split_ifs <;> ring
  have step2b : ∀ t : ℝ, 0 < t → F t * ((D / ENNReal.ofReal t) ^ r *
      ∫⁻ x, {x | h x ≤ ENNReal.ofReal t}.indicator (fun x => h x ^ r) x ∂μ) =
        D ^ r * ∫⁻ x, K2 (x, t) ∂μ := by
    intro t ht
    have hI : Measurable ({x | h x ≤ ENNReal.ofReal t}.indicator (fun x => h x ^ r)) :=
      (hh.pow_const r).indicator (measurableSet_le hh measurable_const)
    rw [ENNReal.div_rpow_of_nonneg _ _ hr0.le, e, hFG2 t ht, ← lintegral_const_mul _ hI]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [hK2def, indicator_apply, mem_setOf_eq]
    split_ifs <;> ring
  have step4a : ∀ x, ∫⁻ t in Ioi (0 : ℝ), K1 (x, t) = h x * (c1 * h x ^ (p - 1)) := by
    intro x
    have hm : Measurable ({t : ℝ | ENNReal.ofReal t < h x}.indicator G1) :=
      hG1.indicator (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    calc ∫⁻ t in Ioi (0 : ℝ), K1 (x, t)
        = ∫⁻ t in Ioi (0 : ℝ), (h x * c1) * {t : ℝ | ENNReal.ofReal t < h x}.indicator G1 t :=
          lintegral_congr fun t => by
            simp only [hK1def, indicator_apply, mem_setOf_eq]
            split_ifs <;> ring
      _ = (h x * c1) * ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < h x}.indicator G1 t :=
          lintegral_const_mul _ hm
      _ = h x * (c1 * h x ^ (p - 1)) := by
          rw [lintegral_Ioi_indicator_rpow (h x) hp1]; ring
  have step4b : ∀ x, ∫⁻ t in Ioi (0 : ℝ), K2 (x, t) = h x ^ r * (c2 * h x ^ (-(r - p))) := by
    intro x
    have hm : Measurable ({t : ℝ | h x ≤ ENNReal.ofReal t}.indicator G2) :=
      hG2.indicator (measurableSet_le measurable_const ENNReal.measurable_ofReal)
    calc ∫⁻ t in Ioi (0 : ℝ), K2 (x, t)
        = ∫⁻ t in Ioi (0 : ℝ), (h x ^ r * c2) * {t : ℝ | h x ≤ ENNReal.ofReal t}.indicator G2 t :=
          lintegral_congr fun t => by
            simp only [hK2def, indicator_apply, mem_setOf_eq]
            split_ifs <;> ring
      _ = (h x ^ r * c2) * ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | h x ≤ ENNReal.ofReal t}.indicator G2 t :=
          lintegral_const_mul _ hm
      _ = h x ^ r * (c2 * h x ^ (-(r - p))) := by
          rw [lintegral_Ioi_indicator_rpow_neg (h x) hrp]; ring
  have swap : ∀ K : X × ℝ → ℝ≥0∞, Measurable K →
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, K (x, t) ∂μ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), K (x, t)) ∂μ :=
    fun K hK => (lintegral_lintegral_swap (f := fun x t => K (x, t)) hK.aemeasurable).symm
  have hpow : ∀ x, h x ^ r * h x ^ (-(r - p)) ≤ h x ^ p := by
    intro x
    rcases eq_or_ne (h x) 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hr0, zero_mul]; exact bot_le
    rcases eq_or_ne (h x) ⊤ with ht | ht
    · rw [ht, ENNReal.top_rpow_of_neg (show -(r - p) < 0 by linarith), mul_zero]; exact bot_le
    rw [← ENNReal.rpow_add _ _ h0 ht, show r + -(r - p) = p by ring]
  have hpow1 : ∀ x, h x * h x ^ (p - 1) = h x ^ p := by
    intro x
    conv_rhs => rw [show p = 1 + (p - 1) by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one hp1.le, ENNReal.rpow_one]
  calc ∫⁻ x, g x ^ p ∂μ
      = ∫⁻ t in Ioi (0 : ℝ), F t * μ {x | ENNReal.ofReal t < g x} := step1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (F t * (C / ENNReal.ofReal t *
          ∫⁻ x, {x | ENNReal.ofReal t < h x}.indicator h x ∂μ) +
          F t * ((D / ENNReal.ofReal t) ^ r *
          ∫⁻ x, {x | h x ≤ ENNReal.ofReal t}.indicator (fun x => h x ^ r) x ∂μ)) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => by
          rw [← mul_add]; exact mul_le_mul_right (H t ht) _
    _ = ∫⁻ t in Ioi (0 : ℝ), (C * ∫⁻ x, K1 (x, t) ∂μ + D ^ r * ∫⁻ x, K2 (x, t) ∂μ) :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [step2a t ht, step2b t ht]
    _ = C * ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), K1 (x, t)) ∂μ +
          D ^ r * ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), K2 (x, t)) ∂μ := by
        have m1 : Measurable fun t => ∫⁻ x, K1 (x, t) ∂μ :=
          (hK1.comp measurable_swap).lintegral_prod_right'
        have m2 : Measurable fun t => ∫⁻ x, K2 (x, t) ∂μ :=
          (hK2.comp measurable_swap).lintegral_prod_right'
        rw [lintegral_add_left (m1.const_mul C), lintegral_const_mul C m1,
          lintegral_const_mul _ m2,
          swap K1 hK1, swap K2 hK2]
    _ ≤ C * ∫⁻ x, c1 * h x ^ p ∂μ + D ^ r * ∫⁻ x, c2 * h x ^ p ∂μ := by
        refine add_le_add (mul_le_mul_right (lintegral_mono fun x => ?_) _)
          (mul_le_mul_right (lintegral_mono fun x => ?_) _)
        · rw [step4a x, ← hpow1 x]; exact le_of_eq (by ring)
        · rw [step4b x]
          calc h x ^ r * (c2 * h x ^ (-(r - p))) = c2 * (h x ^ r * h x ^ (-(r - p))) := by ring
            _ ≤ c2 * h x ^ p := mul_le_mul_right (hpow x) _
    _ = _ := by
        rw [lintegral_const_mul _ (hh.pow_const p), lintegral_const_mul _ (hh.pow_const p)]
        ring

/-- Let `g, h ≥ 0` on an s-finite measure space and `1 < p < r`. If for every `t > 0`
`μ{g > t} ≤ (C/t) ∫_{h > t} h + (D/t)^r ∫_{h ≤ t} h^r`, then
`∫ g^p ≤ (C p/(p-1) + D^r p/(r-p)) ∫ h^p`. -/
lemma lintegral_rpow_le_of_distribution_le_two {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) (C D : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) < h x}.indicator h x ∂μ +
      (D / t) ^ r * ∫⁻ x, {x | h x ≤ t}.indicator (fun x => h x ^ r) x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤
      (C * ENNReal.ofReal (p / (p - 1)) + D ^ r * ENNReal.ofReal (p / (r - p))) *
        ∫⁻ x, h x ^ p ∂μ := by
  have eg := hg.ae_eq_mk
  have eh := hh.ae_eq_mk
  have hL : ∫⁻ x, g x ^ p ∂μ = ∫⁻ x, hg.mk g x ^ p ∂μ :=
    lintegral_congr_ae (eg.mono fun x hx => by simp only [hx])
  have hR : ∫⁻ x, h x ^ p ∂μ = ∫⁻ x, hh.mk h x ^ p ∂μ :=
    lintegral_congr_ae (eh.mono fun x hx => by simp only [hx])
  rw [hL, hR]
  refine lintegral_rpow_le_of_distribution_le_two_of_measurable μ hg.measurable_mk
    hh.measurable_mk hp hpr C D fun t ht => ?_
  have h1 : μ {x | ENNReal.ofReal t < hg.mk g x} = μ {x | ENNReal.ofReal t < g x} :=
    measure_congr (eg.mono fun x hx => by
      change (ENNReal.ofReal t < hg.mk g x) = (ENNReal.ofReal t < g x)
      rw [hx])
  have h2 : ∫⁻ x, {x | ENNReal.ofReal t < hh.mk h x}.indicator (hh.mk h) x ∂μ =
      ∫⁻ x, {x | ENNReal.ofReal t < h x}.indicator h x ∂μ :=
    lintegral_congr_ae (eh.mono fun x hx => by
      simp only [indicator_apply, mem_setOf_eq, hx])
  have h3 : ∫⁻ x, {x | hh.mk h x ≤ ENNReal.ofReal t}.indicator (fun x => hh.mk h x ^ r) x ∂μ =
      ∫⁻ x, {x | h x ≤ ENNReal.ofReal t}.indicator (fun x => h x ^ r) x ∂μ :=
    lintegral_congr_ae (eh.mono fun x hx => by
      simp only [indicator_apply, mem_setOf_eq, hx])
  rw [h1, h2, h3]
  exact H t.toNNReal (Real.toNNReal_pos.2 ht)

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {g h : X → ℝ≥0∞} (hg : AEMeasurable g μ) (hh : AEMeasurable h μ)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) (C D : ℝ≥0∞)
    (H : ∀ t : ℝ≥0, 0 < t → μ {x | (t : ℝ≥0∞) < g x} ≤
      C / t * ∫⁻ x, {x | (t : ℝ≥0∞) < h x}.indicator h x ∂μ +
      (D / t) ^ r * ∫⁻ x, {x | h x ≤ t}.indicator (fun x => h x ^ r) x ∂μ) :
    ∫⁻ x, g x ^ p ∂μ ≤
      (C * ENNReal.ofReal (p / (p - 1)) + D ^ r * ENNReal.ofReal (p / (r - p))) *
        ∫⁻ x, h x ^ p ∂μ :=
  lintegral_rpow_le_of_distribution_le_two μ hg hh hp hpr C D H

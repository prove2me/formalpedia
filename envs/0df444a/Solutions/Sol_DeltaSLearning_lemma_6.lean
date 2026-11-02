-- Prove2me | solution 1 for DeltaSLearning.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:38:17.469417+00:00
-- url     : https://prove2.me/submissions/65c6d332-9714-4f62-a6cd-c3f34ed02975

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential

open MeasureTheory ProbabilityTheory Filter

namespace SolLemma6

lemma exp_sub_one_sub_nonneg (u : ℝ) : 0 ≤ Real.exp u - 1 - u := by
  linarith [Real.add_one_le_exp u]

lemma sinh_ge_self_of_nonneg {v : ℝ} (hv : 0 ≤ v) : v ≤ Real.sinh v := by
  have h_sum := Real.hasSum_sinh v
  have h_le := Summable.le_tsum h_sum.summable 0 (fun k _ => by positivity)
  rw [h_sum.tsum_eq] at h_le
  simpa using h_le

lemma exp_sub_one_sub_le_abs (u : ℝ) :
    Real.exp u - 1 - u ≤ Real.exp |u| - 1 - |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]
    have hsinh : -u ≤ Real.sinh (-u) := sinh_ge_self_of_nonneg (by linarith)
    rw [Real.sinh_eq, neg_neg] at hsinh
    linarith

lemma intervalIntegral_exp_sub_one (a z : ℝ) :
    ∫ t in (0 : ℝ)..z, a * (Real.exp (a * t) - 1) = Real.exp (a * z) - 1 - a * z := by
  let F : ℝ → ℝ := fun t => Real.exp (a * t) - 1 - a * t
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) z,
      HasDerivAt F (a * (Real.exp (a * t) - 1)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => a * s) a t := by
      simpa using (hasDerivAt_id t).const_mul a
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (a * s)) (Real.exp (a * t) * a) t :=
      (Real.hasDerivAt_exp (a * t)).comp t h1
    have h3 : HasDerivAt F (Real.exp (a * t) * a - a) t := (h2.sub_const 1).sub h1
    have h_eq : a * (Real.exp (a * t) - 1) = Real.exp (a * t) * a - a := by ring
    rw [h_eq]
    exact h3
  have hint : IntervalIntegrable (fun t => a * (Real.exp (a * t) - 1)) volume 0 z :=
    (Continuous.const_mul (Continuous.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))
        continuous_const) a).intervalIntegrable 0 z
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  simp

lemma integrable_of_exp_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (c₁ * Real.exp (-(c₂ * t)))) :
    Integrable X P := by
  refine ⟨hX.aestronglyMeasurable, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [Real.norm_eq_abs]
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => abs_nonneg (X ω))]
  have h_lc := lintegral_eq_lintegral_meas_le P (Eventually.of_forall fun ω => abs_nonneg (X ω))
    (measurable_abs.comp hX).aemeasurable
  rw [h_lc]
  have h_le : ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t ≤ |X ω|} ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (c₁ * Real.exp (-c₂ * t)) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    simpa [neg_mul] using htail t ht
  have h_int : IntegrableOn (fun t : ℝ => c₁ * Real.exp (-c₂ * t)) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul c₁
  have h_eq : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (c₁ * Real.exp (-c₂ * t)) =
      ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), c₁ * Real.exp (-c₂ * t)) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal h_int
      (Eventually.of_forall fun t => by positivity)
  exact lt_of_le_of_lt h_le (h_eq ▸ ENNReal.ofReal_lt_top)

lemma lintegral_exp_abs_sub_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (c₁ * Real.exp (-(c₂ * t))))
    (a : ℝ) (ha₀ : 0 ≤ a) (ha : a < c₂) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * |X ω|) - 1 - a * |X ω|) ∂P ≤
      ENNReal.ofReal (c₁ * a ^ 2 / (c₂ * (c₂ - a))) := by
  let g : ℝ → ℝ := fun t => a * (Real.exp (a * t) - 1)
  have hg_cont : Continuous g :=
    continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const)
  have hg_int : ∀ t > 0, IntervalIntegrable g volume 0 t := fun t _ =>
    hg_cont.intervalIntegrable 0 t
  have hg_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    dsimp [g]
    have ht0 : 0 ≤ a * t := mul_nonneg ha₀ (le_of_lt ht)
    have hexp : 1 ≤ Real.exp (a * t) := Real.one_le_exp ht0
    exact mul_nonneg ha₀ (sub_nonneg.mpr hexp)
  have h_lc := lintegral_comp_eq_lintegral_meas_le_mul P
    (Eventually.of_forall fun ω => abs_nonneg (X ω)) (measurable_abs.comp hX).aemeasurable hg_int hg_nonneg
  have h_lhs : (fun ω => ENNReal.ofReal (∫ t in (0 : ℝ)..|X ω|, g t)) =
      fun ω => ENNReal.ofReal (Real.exp (a * |X ω|) - 1 - a * |X ω|) := by
    ext ω
    rw [intervalIntegral_exp_sub_one]
  rw [h_lhs] at h_lc
  rw [h_lc]
  let h : ℝ → ℝ := fun t => c₁ * a * (Real.exp (-(c₂ - a) * t) - Real.exp (-c₂ * t))
  have h_mono : ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | t ≤ |X ω|} * ENNReal.ofReal (g t) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (h t) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht_pos : 0 < t := ht
    have hg_t : 0 ≤ g t := by
      dsimp [g]
      exact mul_nonneg ha₀ (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg ha₀ (le_of_lt ht_pos))))
    have h1 : P {ω | t ≤ |X ω|} * ENNReal.ofReal (g t) ≤
        ENNReal.ofReal (c₁ * Real.exp (-(c₂ * t))) * ENNReal.ofReal (g t) :=
      mul_le_mul_of_nonneg_right (htail t ht_pos) zero_le
    rw [← ENNReal.ofReal_mul (by positivity)] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    dsimp [g, h]
    calc c₁ * Real.exp (-(c₂ * t)) * (a * (Real.exp (a * t) - 1))
      _ = c₁ * a * (Real.exp (-(c₂ * t) + a * t) - Real.exp (-(c₂ * t))) := by
          rw [Real.exp_add]
          ring
      _ = c₁ * a * (Real.exp (-(c₂ - a) * t) - Real.exp (-c₂ * t)) := by
          congr 2 <;> ring
  have h_int1 : IntegrableOn (fun t : ℝ => Real.exp (-(c₂ - a) * t)) (Set.Ioi 0) volume :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h_int2 : IntegrableOn (fun t : ℝ => Real.exp (-c₂ * t)) (Set.Ioi 0) volume :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h_int_h : IntegrableOn h (Set.Ioi 0) volume :=
    (h_int1.sub h_int2).const_mul (c₁ * a)
  have h_nonneg_h : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ h t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht => ?_
    dsimp [h]
    have hle : -c₂ * t ≤ -(c₂ - a) * t := by nlinarith [show (0 : ℝ) < t from ht]
    exact mul_nonneg (mul_nonneg (le_of_lt hc₁) ha₀) (sub_nonneg.mpr (Real.exp_le_exp.mpr hle))
  have h_eq : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (h t) =
      ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), h t) :=
    (ofReal_integral_eq_lintegral_ofReal h_int_h h_nonneg_h).symm
  have h_val : ∫ t in Set.Ioi (0 : ℝ), h t = c₁ * a ^ 2 / (c₂ * (c₂ - a)) := by
    dsimp [h]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub h_int1 h_int2,
      integral_exp_mul_Ioi (by linarith) 0, integral_exp_mul_Ioi (by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    have hc2_ne : c₂ ≠ 0 := ne_of_gt hc₂
    have hca_ne : c₂ - a ≠ 0 := ne_of_gt (sub_pos.mpr ha)
    field_simp
    ring
  rw [h_eq, h_val] at h_mono
  exact h_mono

end SolLemma6

open SolLemma6

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hmean : ∫ ω, X ω ∂P = 0) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (c₁ * Real.exp (-(c₂ * t)))) :
    HighDimStat.TailBounds.IsSubExponential X P (2 * Real.sqrt c₁ / c₂) (2 / c₂) := by
  have hX_int : Integrable X P := integrable_of_exp_tail P X hX c₁ c₂ hc₁ hc₂ htail
  have h_Range : ∀ lam : ℝ, (2 / c₂ = 0 ∨ |lam| < 1 / (2 / c₂)) → |lam| < c₂ / 2 := by
    intro lam hlam
    rcases hlam with h0 | hlt
    · exfalso
      have : (0 : ℝ) < 2 / c₂ := by positivity
      linarith
    · have : 1 / (2 / c₂) = c₂ / 2 := by field_simp
      linarith
  have h_rem_int : ∀ lam : ℝ, |lam| < c₂ / 2 →
      Integrable (fun ω => Real.exp (|lam| * |X ω|) - 1 - |lam| * |X ω|) P := by
    intro lam hlam
    have ha : |lam| < c₂ := by linarith
    have h_meas : Measurable (fun ω => Real.exp (|lam| * |X ω|) - 1 - |lam| * |X ω|) :=
      ((Real.continuous_exp.measurable.comp (measurable_const.mul hX.norm)).sub measurable_const).sub
        (measurable_const.mul hX.norm)
    refine ⟨h_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => exp_sub_one_sub_nonneg (|lam| * |X ω|))]
    exact lt_of_le_of_lt (lintegral_exp_abs_sub_le P X hX c₁ c₂ hc₁ hc₂ htail |lam| (abs_nonneg lam) ha)
      ENNReal.ofReal_lt_top
  have h_exp_int : ∀ lam : ℝ, |lam| < c₂ / 2 →
      Integrable (fun ω => Real.exp (lam * X ω)) P := by
    intro lam hlam
    have h_dom_int : Integrable (fun ω => Real.exp (|lam| * |X ω|)) P := by
      have h1 := ((h_rem_int lam hlam).add (integrable_const (1 : ℝ))).add (hX_int.norm.const_mul |lam|)
      refine h1.congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      ring
    have h_meas : Measurable (fun ω => Real.exp (lam * X ω)) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul hX)
    refine h_dom_int.mono' h_meas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc lam * X ω ≤ |lam * X ω| := le_abs_self _
      _ = |lam| * |X ω| := abs_mul lam (X ω)
  refine ⟨hX_int, ?_, ?_⟩
  · intro lam hlam
    simp only [hmean, sub_zero]
    exact h_exp_int lam (h_Range lam hlam)
  · intro lam hlam
    simp only [hmean, sub_zero]
    have hlam_lt : |lam| < c₂ / 2 := h_Range lam hlam
    have ha : |lam| < c₂ := by linarith
    have h_int_lam : Integrable (fun ω => Real.exp (lam * X ω)) P := h_exp_int lam hlam_lt
    have h_int_sub : Integrable (fun ω => Real.exp (lam * X ω) - 1 - lam * X ω) P :=
      (h_int_lam.sub (integrable_const (1 : ℝ))).sub (hX_int.const_mul lam)
    have h_int_abs : Integrable (fun ω => Real.exp (|lam| * |X ω|) - 1 - |lam| * |X ω|) P :=
      h_rem_int lam hlam_lt
    have h_le1 : ∫ ω, (Real.exp (lam * X ω) - 1 - lam * X ω) ∂P ≤
        ∫ ω, (Real.exp (|lam| * |X ω|) - 1 - |lam| * |X ω|) ∂P := by
      refine integral_mono h_int_sub h_int_abs fun ω => ?_
      have h := exp_sub_one_sub_le_abs (lam * X ω)
      simpa [abs_mul] using h
    have h_le2 : ∫ ω, (Real.exp (|lam| * |X ω|) - 1 - |lam| * |X ω|) ∂P ≤
        c₁ * |lam| ^ 2 / (c₂ * (c₂ - |lam|)) := by
      have h_lint := lintegral_exp_abs_sub_le P X hX c₁ c₂ hc₁ hc₂ htail |lam| (abs_nonneg lam) ha
      have h_eq := ofReal_integral_eq_lintegral_ofReal h_int_abs
        (Eventually.of_forall fun ω => exp_sub_one_sub_nonneg (|lam| * |X ω|))
      rw [← h_eq] at h_lint
      exact (ENNReal.ofReal_le_ofReal_iff (by
        have : 0 < c₂ - |lam| := sub_pos.mpr ha
        positivity)).mp h_lint
    have h_le3 : c₁ * |lam| ^ 2 / (c₂ * (c₂ - |lam|)) ≤ (2 * Real.sqrt c₁ / c₂) ^ 2 * lam ^ 2 / 2 := by
      rw [sq_abs]
      have h_denom : c₂ * (c₂ / 2) ≤ c₂ * (c₂ - |lam|) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hc₂)
      have h_div : c₁ * lam ^ 2 / (c₂ * (c₂ - |lam|)) ≤ c₁ * lam ^ 2 / (c₂ * (c₂ / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h_denom
      have h_rhs : c₁ * lam ^ 2 / (c₂ * (c₂ / 2)) = (2 * Real.sqrt c₁ / c₂) ^ 2 * lam ^ 2 / 2 := by
        have hc2_ne : c₂ ≠ 0 := ne_of_gt hc₂
        rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hc₁)]
        field_simp
      exact h_div.trans_eq h_rhs
    have h_split : ∫ ω, (Real.exp (lam * X ω) - 1 - lam * X ω) ∂P =
        (∫ ω, Real.exp (lam * X ω) ∂P) - 1 := by
      have h1 := integral_sub (h_int_lam.sub (integrable_const (1 : ℝ))) (hX_int.const_mul lam)
      have h2 := integral_sub h_int_lam (integrable_const (1 : ℝ))
      simp only [Pi.sub_apply] at h1 h2
      rw [h1, h2, integral_const_mul, hmean, mul_zero, sub_zero]
      simp
    have h_exp_bound : ∫ ω, Real.exp (lam * X ω) ∂P ≤
        (2 * Real.sqrt c₁ / c₂) ^ 2 * lam ^ 2 / 2 + 1 := by
      linarith
    exact h_exp_bound.trans (Real.add_one_le_exp _)

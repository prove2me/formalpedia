-- Prove2me | solution 1 for BanditAlgorithm.le_cam_inequality
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-19T01:48:36.962631+00:00
-- url     : https://prove2.me/submissions/53bb54d3-4165-4fc3-9277-743276a4216e

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory InformationTheory
open scoped ENNReal

theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (2⁻¹ * Real.exp (-(klDiv P Q).toReal)) ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  let ν := P + Q
  let p := fun ω ↦ P.rnDeriv ν ω
  let q := fun ω ↦ Q.rnDeriv ν ω
  let affinity := ∫⁻ ω, min (p ω) (q ω) ∂ν
  let hellingerProduct := ∫⁻ ω, (p ω * q ω) ^ (1 / 2 : ℝ) ∂ν
  let hellingerMinMax := ∫⁻ ω, (min (p ω) (q ω)) ^ (1 / 2 : ℝ) *
    (max (p ω) (q ω)) ^ (1 / 2 : ℝ) ∂ν
  have density_half_identity (a b : ℝ≥0∞) (ha_top : a ≠ ∞)
      (hb_pos : b ≠ 0) (hb_top : b ≠ ∞) :
      a.toReal * Real.exp (-Real.log ((a / b).toReal) / 2) =
        ((a * b) ^ (1 / 2 : ℝ)).toReal := by
    by_cases ha : a = 0
    · simp [ha]
    have haR : 0 < a.toReal := ENNReal.toReal_pos ha ha_top
    have hbR : 0 < b.toReal := ENNReal.toReal_pos hb_pos hb_top
    rw [ENNReal.toReal_div, ← ENNReal.toReal_rpow, ENNReal.toReal_mul]
    rw [Real.exp_half, Real.exp_neg, Real.exp_log (div_pos haR hbR)]
    rw [inv_div, Real.sqrt_div (le_of_lt hbR), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (le_of_lt haR)]
    field_simp [Real.sqrt_ne_zero'.mpr haR, Real.sqrt_ne_zero'.mpr hbR]
    nlinarith [Real.sq_sqrt haR.le, Real.sq_sqrt hbR.le]
  have hJ : Real.exp (-(klDiv P Q).toReal / 2) ≤
      ∫ ω, Real.exp (-llr P Q ω / 2) ∂P := by
    have hD' := klDiv_ne_top_iff.mp hD
    have hPQ : P ≪ Q := hD'.1
    have hllr : Integrable (llr P Q) P := hD'.2
    have hDreal : (klDiv P Q).toReal = ∫ ω, llr P Q ω ∂P := by
      simpa using toReal_klDiv hPQ hllr
    have hrn : Integrable (fun ω ↦ (Q.rnDeriv P ω).toReal) P :=
      Measure.integrable_toReal_rnDeriv
    have hsqrt : Integrable (fun ω ↦ Real.sqrt (Q.rnDeriv P ω).toReal) P := by
      apply integrable_of_le_of_le
        ((Measure.measurable_rnDeriv Q P).ennreal_toReal.sqrt.aestronglyMeasurable)
        (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _) (ae_of_all _ fun ω ↦ ?_)
        (integrable_zero _ _ _) ((integrable_const (1 : ℝ)).add hrn)
      change Real.sqrt (Q.rnDeriv P ω).toReal ≤ 1 + (Q.rnDeriv P ω).toReal
      have hsq := Real.sq_sqrt
        (ENNReal.toReal_nonneg : 0 ≤ (Q.rnDeriv P ω).toReal)
      have hsnonneg := Real.sqrt_nonneg (Q.rnDeriv P ω).toReal
      have hrnonneg :=
        (ENNReal.toReal_nonneg : 0 ≤ (Q.rnDeriv P ω).toReal)
      nlinarith [sq_nonneg (Real.sqrt (Q.rnDeriv P ω).toReal - 1)]
    have hexp_sqrt :
        (fun ω ↦ Real.exp (-llr P Q ω / 2)) =ᵐ[P]
          fun ω ↦ Real.sqrt (Q.rnDeriv P ω).toReal := by
      filter_upwards [exp_neg_llr hPQ] with ω hω
      rw [Real.exp_half, hω]
    have hexp : Integrable (fun ω ↦ Real.exp (-llr P Q ω / 2)) P :=
      (integrable_congr hexp_sqrt).mpr hsqrt
    have hjensen := convexOn_exp.map_integral_le Real.continuousOn_exp isClosed_univ
      (ae_of_all _ fun _ ↦ Set.mem_univ _) (hllr.neg.div_const 2) hexp
    rw [integral_div] at hjensen
    have hnegint : (∫ a, (-llr P Q) a ∂P) = -(∫ a, llr P Q a ∂P) := by
      simpa only [Pi.neg_apply] using integral_neg (μ := P) (f := llr P Q)
    rw [hnegint] at hjensen
    simpa only [Function.comp_apply, Pi.neg_apply, integral_div, hDreal] using hjensen
  have hbridge : (∫ ω, Real.exp (-llr P Q ω / 2) ∂P) =
      hellingerProduct.toReal := by
    have hD' := klDiv_ne_top_iff.mp hD
    have hPQ : P ≪ Q := hD'.1
    have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
    have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
    have hνQ : ν ≪ Q := hPQ.add_left Measure.AbsolutelyContinuous.rfl
    have hratioQ : P.rnDeriv Q =ᵐ[Q] fun ω ↦ p ω / q ω :=
      Measure.rnDeriv_eq_div hPν hQν
    have hratio : P.rnDeriv Q =ᵐ[ν] fun ω ↦ p ω / q ω := hνQ hratioQ
    have hp_top : ∀ᵐ ω ∂ν, p ω ≠ ∞ :=
      (Measure.rnDeriv_lt_top P ν).mono fun _ h ↦ h.ne
    have hq_top : ∀ᵐ ω ∂ν, q ω ≠ ∞ :=
      (Measure.rnDeriv_lt_top Q ν).mono fun _ h ↦ h.ne
    have hq_pos_Q : ∀ᵐ ω ∂Q, 0 < q ω := Measure.rnDeriv_pos hQν
    have hq_pos : ∀ᵐ ω ∂ν, 0 < q ω := hνQ hq_pos_Q
    have heq :
        (fun ω ↦ (p ω).toReal * Real.exp (-llr P Q ω / 2)) =ᵐ[ν]
          fun ω ↦ ((p ω * q ω) ^ (1 / 2 : ℝ)).toReal := by
      filter_upwards [hratio, hp_top, hq_top, hq_pos] with ω hratio hp_top hq_top hq_pos
      simpa only [llr, hratio] using
        density_half_identity (p ω) (q ω) hp_top hq_pos.ne' hq_top
    have hmeas : AEMeasurable (fun ω ↦ (p ω * q ω) ^ (1 / 2 : ℝ)) ν := by
      fun_prop
    have hfinite : ∀ᵐ ω ∂ν, (p ω * q ω) ^ (1 / 2 : ℝ) < ∞ := by
      filter_upwards [hp_top, hq_top] with ω hp_top hq_top
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_ne_top hp_top hq_top)
    calc
      ∫ ω, Real.exp (-llr P Q ω / 2) ∂P =
          ∫ ω, (p ω).toReal * Real.exp (-llr P Q ω / 2) ∂ν := by
        symm
        exact integral_toReal_rnDeriv_mul hPν
      _ = ∫ ω, ((p ω * q ω) ^ (1 / 2 : ℝ)).toReal ∂ν :=
        integral_congr_ae heq
      _ = hellingerProduct.toReal := by
        rw [integral_toReal hmeas hfinite]
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have ha_one : affinity ≤ 1 := by
    calc
      affinity ≤ ∫⁻ ω, p ω ∂ν := lintegral_mono fun ω ↦ min_le_left _ _
      _ = P Set.univ := Measure.lintegral_rnDeriv hPν
      _ = 1 := by norm_num
  have ha_top : affinity ≠ ∞ := (lt_of_le_of_lt ha_one ENNReal.one_lt_top).ne
  have hhellinger : hellingerProduct = hellingerMinMax := by
    apply lintegral_congr
    intro ω
    calc
      (p ω * q ω) ^ (1 / 2 : ℝ) =
          (min (p ω) (q ω) * max (p ω) (q ω)) ^ (1 / 2 : ℝ) := by
        rw [min_mul_max]
      _ = (min (p ω) (q ω)) ^ (1 / 2 : ℝ) *
          (max (p ω) (q ω)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        positivity
  have hC : hellingerMinMax ^ (2 : ℝ) ≤ 2 * affinity := by
    let opposite := ∫⁻ ω, max (p ω) (q ω) ∂ν
    have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
    have hp : AEMeasurable p ν := (Measure.measurable_rnDeriv _ _).aemeasurable
    have hq : AEMeasurable q ν := (Measure.measurable_rnDeriv _ _).aemeasurable
    have hmin : AEMeasurable (fun ω ↦ min (p ω) (q ω)) ν := hp.min hq
    have hmax : AEMeasurable (fun ω ↦ max (p ω) (q ω)) ν := hp.max hq
    have hsum : affinity + opposite = 2 := by
      calc
        affinity + opposite = ∫⁻ ω, min (p ω) (q ω) + max (p ω) (q ω) ∂ν := by
          rw [lintegral_add_left' hmin]
        _ = ∫⁻ ω, p ω + q ω ∂ν := by
          apply lintegral_congr
          intro ω
          exact min_add_max (p ω) (q ω)
        _ = (∫⁻ ω, p ω ∂ν) + ∫⁻ ω, q ω ∂ν := lintegral_add_left' hp _
        _ = P Set.univ + Q Set.univ := by
          rw [Measure.lintegral_rnDeriv hPν, Measure.lintegral_rnDeriv hQν]
        _ = 2 := by norm_num
    have hopposite : opposite ≤ 2 := by
      calc
        opposite ≤ affinity + opposite := le_add_left le_rfl
        _ = 2 := hsum
    have hholder : hellingerMinMax ≤
        affinity ^ (1 / 2 : ℝ) * opposite ^ (1 / 2 : ℝ) := by
      exact ENNReal.lintegral_mul_norm_pow_le hmin hmax
        (by positivity) (by positivity) (by norm_num)
    calc
      hellingerMinMax ^ (2 : ℝ) ≤
          (affinity ^ (1 / 2 : ℝ) * opposite ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        gcongr
      _ = affinity * opposite := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
      _ ≤ affinity * 2 := by gcongr
      _ = 2 * affinity := mul_comm _ _
  rw [hbridge, hhellinger] at hJ
  have hright_top : 2 * affinity ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ha_top
  have hCreal := ENNReal.toReal_mono hright_top hC
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul] at hCreal
  norm_num at hCreal
  have hexp_sq : Real.exp (-(klDiv P Q).toReal) =
      Real.exp (-(klDiv P Q).toReal / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (ENNReal.ofReal_le_iff_le_toReal ha_top).2
  rw [hexp_sq]
  have hexp_nonneg : 0 ≤ Real.exp (-(klDiv P Q).toReal / 2) := (Real.exp_pos _).le
  have hhellinger_nonneg : 0 ≤ hellingerMinMax.toReal := ENNReal.toReal_nonneg
  nlinarith

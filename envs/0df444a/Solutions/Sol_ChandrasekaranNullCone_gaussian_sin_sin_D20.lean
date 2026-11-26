-- Prove2me | solution 1 for ChandrasekaranNullCone.gaussian_sin_sin_D20
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T15:32:55.528964+00:00
-- url     : https://prove2.me/submissions/09d3c39b-4c6a-4711-a4de-a7936b3181e4

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MeasureTheory ProbabilityTheory

namespace ChandrasekaranNullCone.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `cos ∘ W` is integrable for any a.e.-measurable `W` under a probability measure. -/
lemma integrable_cos_comp [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : AEMeasurable W P) :
    Integrable (fun ω => Real.cos (W ω)) P := by
  refine (integrable_const (1 : ℝ)).mono'
    (Real.continuous_cos.measurable.comp_aemeasurable hW).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _

/-- `E[cos W] = exp(-Var W / 2)` for a centred real Gaussian `W`. -/
lemma integral_cos_of_hasGaussianLaw {W : Ω → ℝ} (hW : HasGaussianLaw W P) (h0 : P[W] = 0) :
    ∫ ω, Real.cos (W ω) ∂P = Real.exp (-(Var[W; P]) / 2) := by
  have hmeas := hW.aemeasurable
  rw [← integral_map hmeas Real.continuous_cos.aestronglyMeasurable, hW.map_eq_gaussianReal, h0]
  set v := Var[W; P].toNNReal with hv
  have hc := charFun_gaussianReal (μ := 0) (v := v) 1
  rw [charFun_apply_real] at hc
  have hint : Integrable (fun x : ℝ => Complex.exp (((1 : ℝ) : ℂ) * x * Complex.I))
      (gaussianReal 0 v) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [show ((1 : ℝ) : ℂ) * x * Complex.I = ((1 * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
  have hre : ∫ x, Real.cos x ∂(gaussianReal 0 v)
      = (∫ x, Complex.exp (((1 : ℝ) : ℂ) * x * Complex.I) ∂(gaussianReal 0 v)).re := by
    have hcomm := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at hcomm
    rw [← hcomm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.ofReal_one, one_mul]
    exact (Complex.exp_ofReal_mul_I_re x).symm
  rw [hre, hc]
  have hvv : (v : ℝ) = Var[W; P] := Real.coe_toNNReal _ (variance_nonneg W P)
  rw [show ((1 : ℝ) : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((v : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2
      = ((-(v : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.exp_ofReal_re, hvv]

/-- Mean and variance of a linear combination of a centred jointly Gaussian pair. -/
lemma mean_var_lin (X Y : Ω → ℝ) (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX : ∫ ω, X ω ∂P = 0) (hY : ∫ ω, Y ω ∂P = 0) (a b : ℝ) :
    P[fun ω => a * X ω + b * Y ω] = 0 ∧
      Var[fun ω => a * X ω + b * Y ω; P]
        = a ^ 2 * ∫ ω, X ω ^ 2 ∂P + 2 * a * b * ∫ ω, X ω * Y ω ∂P + b ^ 2 * ∫ ω, Y ω ^ 2 ∂P := by
  have hP := hXY.isProbabilityMeasure
  have hXm := hXY.fst.memLp_two
  have hYm := hXY.snd.memLp_two
  have hXi := hXY.fst.integrable
  have hYi := hXY.snd.integrable
  have hmean : P[fun ω => a * X ω + b * Y ω] = 0 := by
    rw [integral_add (hXi.const_mul a) (hYi.const_mul b), integral_const_mul, integral_const_mul,
      hX, hY]; ring
  refine ⟨hmean, ?_⟩
  have hW : AEMeasurable (fun ω => a * X ω + b * Y ω) P :=
    (hXY.fst.aemeasurable.const_mul a).add (hXY.snd.aemeasurable.const_mul b)
  rw [variance_of_integral_eq_zero hW hmean]
  have hX2 := hXm.integrable_sq
  have hY2 := hYm.integrable_sq
  have hXY2 : Integrable (fun ω => X ω * Y ω) P := hXm.integrable_mul hYm
  have : (fun ω => (a * X ω + b * Y ω) ^ 2)
      = fun ω => (a ^ 2 * X ω ^ 2 + 2 * a * b * (X ω * Y ω)) + b ^ 2 * Y ω ^ 2 := by
    funext ω; ring
  rw [this, integral_add (f := fun ω => a ^ 2 * X ω ^ 2 + 2 * a * b * (X ω * Y ω))
      (g := fun ω => b ^ 2 * Y ω ^ 2) ((hX2.const_mul _).add (hXY2.const_mul _)) (hY2.const_mul _),
    integral_add (f := fun ω => a ^ 2 * X ω ^ 2) (g := fun ω => 2 * a * b * (X ω * Y ω))
      (hX2.const_mul _) (hXY2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]

end ChandrasekaranNullCone.Gauss

open ChandrasekaranNullCone.Gauss in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX : ∫ ω, X ω ∂P = 0) (hY : ∫ ω, Y ω ∂P = 0)
    (G_LL G_RR G_LR : ℝ) (hLL : ∫ ω, X ω ^ 2 ∂P = G_LL) (hRR : ∫ ω, Y ω ^ 2 ∂P = G_RR)
    (hLR : ∫ ω, X ω * Y ω ∂P = G_LR) (j_L j_R : ℝ) :
    ∫ ω, Real.sin (j_L * X ω) * Real.sin (j_R * Y ω) ∂P
      = Real.exp (-(j_L ^ 2 * G_LL + j_R ^ 2 * G_RR) / 2) * Real.sinh (j_L * j_R * G_LR) := by
  have hP := hXY.isProbabilityMeasure
  -- `E cos(aX + bY)` for any real `a, b`
  have hcos : ∀ a b : ℝ, ∫ ω, Real.cos (a * X ω + b * Y ω) ∂P
      = Real.exp (-(a ^ 2 * G_LL + 2 * a * b * G_LR + b ^ 2 * G_RR) / 2) := by
    intro a b
    have hW : HasGaussianLaw (fun ω => a * X ω + b * Y ω) P := by
      have := hXY.map_fun ((a • ContinuousLinearMap.fst ℝ ℝ ℝ) + (b • ContinuousLinearMap.snd ℝ ℝ ℝ))
      simpa using this
    obtain ⟨h0, hvar⟩ := mean_var_lin X Y hXY hX hY a b
    rw [integral_cos_of_hasGaussianLaw hW h0, hvar, hLL, hRR, hLR]
  have hmeas : ∀ a b : ℝ, AEMeasurable (fun ω => a * X ω + b * Y ω) P := fun a b =>
    (hXY.fst.aemeasurable.const_mul a).add (hXY.snd.aemeasurable.const_mul b)
  -- product to sum
  have hps : (fun ω => Real.sin (j_L * X ω) * Real.sin (j_R * Y ω))
      = fun ω => (Real.cos (j_L * X ω + (-j_R) * Y ω) - Real.cos (j_L * X ω + j_R * Y ω)) / 2 := by
    funext ω
    rw [show j_L * X ω + -j_R * Y ω = j_L * X ω - j_R * Y ω by ring, Real.cos_sub, Real.cos_add]
    ring
  rw [hps, integral_div, integral_sub (integrable_cos_comp (hmeas _ _)) (integrable_cos_comp (hmeas _ _)),
    hcos, hcos, Real.sinh_eq]
  have e1 : Real.exp (-(j_L ^ 2 * G_LL + 2 * j_L * -j_R * G_LR + (-j_R) ^ 2 * G_RR) / 2)
      = Real.exp (-(j_L ^ 2 * G_LL + j_R ^ 2 * G_RR) / 2) * Real.exp (j_L * j_R * G_LR) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(j_L ^ 2 * G_LL + 2 * j_L * j_R * G_LR + j_R ^ 2 * G_RR) / 2)
      = Real.exp (-(j_L ^ 2 * G_LL + j_R ^ 2 * G_RR) / 2) * Real.exp (-(j_L * j_R * G_LR)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  ring

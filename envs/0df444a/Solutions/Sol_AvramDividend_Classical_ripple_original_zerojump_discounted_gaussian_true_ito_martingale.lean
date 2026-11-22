-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_true_ito_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:25:22.877549+00:00
-- url     : https://prove2.me/submissions/629252d5-ea56-4c7d-889c-7f2e57d48c3a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_stopped_gaussian_true_ito_martingale
import Theorems.Thm_AvramDividend_Classical_ripple_LevyStochCalc_progressive_joint_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hqnonneg : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    let H : Ω → ℝ → ℝ := fun ω s =>
      Real.exp (-(q * max 0 s)) * S.indicator G (Real.toNNReal s,ω)
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (Fr : Filtration ℝ mΩ)
      (hFr : ∀ t : ℝ, Fr t = 𝓕.rightCont (Real.toNNReal t))
      (hBrown : LevyStochCalc.Brownian.IsBrownianFiltration B Fr)
      (hB : ∀ (t : ℝ) (ω : Ω), B.W t ω =
        (X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.c) / X.σ)
      (hτFr : IsStoppingTime Fr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)))
      (hm : Measurable (Function.uncurry H))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable Fr H)
      (hq : ∀ (t : ℝ), 0 < t →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) t,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      Martingale
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          B Fr hBrown H hm hp hq) Fr P := by
  classical
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
  let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
    (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
    (p.1 : WithTop ℝ≥0) ≤ τ p.2}
  let H0 : Ω → ℝ → ℝ := fun ω s =>
    S.indicator G (Real.toNNReal s,ω)
  let H : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * max 0 s)) * H0 ω s
  obtain ⟨B,Fr,hFr,hBrown,hB,hτFr,hm0,hp0,hq0,hM0⟩ :=
    ripple_original_zerojump_stopped_gaussian_true_ito_martingale
      X hBV hν x D hD w a b u v hw hau huv hvb T σ τ hσstop hτstop
  have hpScalar : LevyStochCalc.Probability.ProgressivelyMeasurable Fr
      (fun _ s => Real.exp (-(q * max 0 s))) := by
    intro t
    letI : MeasurableSpace Ω := Fr t
    have ht : Measurable (fun s : ℝ =>
        Real.exp (-(q * max 0 s))) := by fun_prop
    exact ((ht.indicator measurableSet_Iic).comp measurable_snd).stronglyMeasurable
  have hp : LevyStochCalc.Probability.ProgressivelyMeasurable Fr H :=
    hpScalar.mul hp0
  have hm : Measurable (Function.uncurry H) :=
    ripple_LevyStochCalc_progressive_joint_measurable Fr H hp
  have hScalar (s : ℝ) : Real.exp (-(q * max 0 s)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ max 0 s := le_max_left 0 s
    nlinarith [mul_nonneg hqnonneg ht]
  have hAbs (ω : Ω) (s : ℝ) : |H ω s| ≤ |H0 ω s| := by
    dsimp [H]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [hScalar s, abs_nonneg (H0 ω s)]
  have hNorm (ω : Ω) (s : ℝ) :
      (‖H ω s‖₊ : ℝ≥0∞) ≤ (‖H0 ω s‖₊ : ℝ≥0∞) := by
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.norm_eq_abs] using hAbs ω s
  have hq : ∀ t : ℝ, 0 < t →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro t ht
    calc
      _ ≤ (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) t,
            (‖H0 ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
          apply lintegral_mono
          intro ω
          apply lintegral_mono
          intro s
          exact ENNReal.pow_le_pow_left (hNorm ω s)
      _ < ⊤ := hq0 t ht
  refine ⟨B,Fr,hFr,hBrown,hB,hτFr,hm,hp,hq,?_⟩
  exact LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian
    B Fr hBrown H hm hp hq

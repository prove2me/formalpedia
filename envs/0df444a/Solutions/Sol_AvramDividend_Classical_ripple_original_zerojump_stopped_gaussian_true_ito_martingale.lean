-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_stopped_gaussian_true_ito_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:28.908087+00:00
-- url     : https://prove2.me/submissions/b1de3bcd-7ae4-450f-b53f-74fc9f76481e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_real_Brownian_stopped_progressive_L2
import Theorems.Thm_AvramDividend_Classical_ripple_original_stopped_gaussian_real_all_horizon_energy
import Theorems.Thm_AvramDividend_Classical_ripple_LevyStochCalc_progressive_joint_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
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
      S.indicator G (Real.toNNReal s,ω)
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
  let H : Ω → ℝ → ℝ := fun ω s =>
    S.indicator G (Real.toNNReal s,ω)
  obtain ⟨B, Fr, μ, hμ, hPhysical, hFr, hBrown, hB, hτFr, hp, hLp⟩ :=
    ripple_original_zerojump_real_Brownian_stopped_progressive_L2
      X hBV hν x D hD w a b u v hw hau huv hvb T σ τ hσstop hτstop
  have hm : Measurable (Function.uncurry H) :=
    ripple_LevyStochCalc_progressive_joint_measurable Fr H hp
  have hq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    ripple_original_stopped_gaussian_real_all_horizon_energy
      X x D w a b u v hw hau huv hvb σ τ
  have hM : Martingale
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
        B Fr hBrown H hm hp hq) Fr P :=
    LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian
      B Fr hBrown H hm hp hq
  exact ⟨B,Fr,hFr,hBrown,hB,hτFr,hm,hp,hq,hM⟩

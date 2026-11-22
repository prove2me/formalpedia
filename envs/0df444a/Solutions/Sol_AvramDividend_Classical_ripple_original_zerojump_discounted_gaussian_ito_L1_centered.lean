-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_zerojump_discounted_gaussian_ito_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:36:56.905807+00:00
-- url     : https://prove2.me/submissions/9c027224-6f7e-4218-85c6-d3683d1fe0d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_discounted_gaussian_true_ito_martingale
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
      ∀ (t : ℝ), 0 ≤ t →
        Integrable
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            B Fr hBrown H hm hp hq t) P ∧
        (∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          B Fr hBrown H hm hp hq t ω ∂P) = 0 := by
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
    Real.exp (-(q * max 0 s)) * S.indicator G (Real.toNNReal s,ω)
  obtain ⟨B,Fr,hFr,hBrown,hB,hτFr,hm,hp,hq,hMart⟩ :=
    ripple_original_zerojump_discounted_gaussian_true_ito_martingale
      X hBV hν q hqnonneg x D hD w a b u v hw hau huv hvb T σ τ hσstop hτstop
  let M : ℝ → Ω → ℝ :=
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      B Fr hBrown H hm hp hq
  have hZero : M (-1) =ᵐ[P] (0 : Ω → ℝ) :=
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg
      B Fr hBrown H hm hp hq (by norm_num)
  refine ⟨B,Fr,hFr,hBrown,hB,hτFr,hm,hp,hq,?_⟩
  intro t ht
  have hInt : Integrable (M t) P := hMart.integrable t
  have hComparison : (-1 : ℝ) ≤ t := by linarith
  have hCond : condExp (Fr (-1)) P (M t) =ᵐ[P] M (-1) :=
    hMart.condExp_ae_eq hComparison
  have hEq : (∫ ω, M t ω ∂P) = (∫ ω, M (-1) ω ∂P) := by
    calc
      _ = ∫ ω, condExp (Fr (-1)) P (M t) ω ∂P :=
        (integral_condExp (Fr.le (-1))).symm
      _ = ∫ ω, M (-1) ω ∂P := integral_congr_ae hCond
  have hInit : (∫ ω, M (-1) ω ∂P) = 0 := by
    rw [integral_congr_ae hZero]
    simp
  exact ⟨hInt, hEq.trans hInit⟩

-- Prove2me | solution 1 for AvramDividend.Classical.levy_condExp_lipschitz_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:53:18.65393+00:00
-- url     : https://prove2.me/submissions/e2c30965-7134-4975-a162-99bf70be05e7

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_absolute_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable
      (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    (∫ ω, |(P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
      (P[(fun η => f (W η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P) ≤
      ∫ ω, L * |Z ω - W ω| ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let FZ : Ω → ℝ := fun ω => f (Z ω + (X.X t ω - X.X s ω))
  let FW : Ω → ℝ := fun ω => f (W ω + (X.X t ω - X.X s ω))
  let H : Ω → ℝ := fun ω => L * |Z ω - W ω|
  have hZE : Integrable (P[FZ | 𝓕 s]) P := integrable_condExp
  have hWE : Integrable (P[FW | 𝓕 s]) P := integrable_condExp
  have hHE : Integrable (P[H | 𝓕 s]) P := integrable_condExp
  have hAbs : Integrable
      (fun ω => |(P[FZ | 𝓕 s]) ω - (P[FW | 𝓕 s]) ω|) P :=
    (hZE.sub hWE).abs
  have hPoint :
      (fun ω => |(P[FZ | 𝓕 s]) ω - (P[FW | 𝓕 s]) ω|) ≤ᵐ[P]
        P[H | 𝓕 s] :=
    levy_condExp_lipschitz_absolute_bound X s t f L hLip Z W hZ hW hDom
  have hInt :=
    integral_mono_ae hAbs hHE hPoint
  calc
    (∫ ω, |(P[FZ | 𝓕 s]) ω - (P[FW | 𝓕 s]) ω| ∂P) ≤
        ∫ ω, (P[H | 𝓕 s]) ω ∂P := hInt
    _ = ∫ ω, H ω ∂P := integral_condExp (𝓕.le s)

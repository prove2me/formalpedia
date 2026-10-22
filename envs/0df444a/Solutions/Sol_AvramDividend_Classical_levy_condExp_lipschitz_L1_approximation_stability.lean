-- Prove2me | solution 1 for AvramDividend.Classical.levy_condExp_lipschitz_L1_approximation_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:07:09.229171+00:00
-- url     : https://prove2.me/submissions/92416fce-dc3c-4edd-85f3-64974d40c63d

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_integral_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z : Ω → ℝ) (Zn : ℕ → Ω → ℝ)
    (hZ : Integrable (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable
      (fun ω => f (Zn n ω + (X.X t ω - X.X s ω))) P)
    (hDom : ∀ n, Integrable (fun ω => L * |Zn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Zn n ω - Z ω| ∂P) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, |(P[(fun η =>
            f (Zn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
          (P[(fun η =>
            f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P)
      atTop (nhds 0) := by
  have hnonneg (n : ℕ) :
      0 ≤ ∫ ω, |(P[(fun η =>
          f (Zn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η =>
          f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P := by
    exact integral_nonneg (fun ω => abs_nonneg _)
  have hupper (n : ℕ) :
      (∫ ω, |(P[(fun η =>
          f (Zn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η =>
          f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P) ≤
      ∫ ω, L * |Zn n ω - Z ω| ∂P :=
    levy_condExp_lipschitz_integral_bound
      X s t f L hLip (Zn n) Z (hZn n) hZ (hDom n)
  exact squeeze_zero hnonneg hupper hlim
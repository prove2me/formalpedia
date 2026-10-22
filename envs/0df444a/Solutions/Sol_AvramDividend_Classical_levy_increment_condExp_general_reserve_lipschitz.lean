-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:17:49.773373+00:00
-- url     : https://prove2.me/submissions/2e1c83c5-7d0d-4028-981f-23318954b208

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_L1_approximation_stability
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_L1_continuity
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_of_simple_L1

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
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Sn : ℕ → SimpleFunc Ω ℝ) (Z : Ω → ℝ)
    (hSn : ∀ n, Measurable[𝓕 s] (Sn n : Ω → ℝ))
    (hZ : Integrable (fun ω =>
      f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable (fun ω =>
      f (Sn n ω + (X.X t ω - X.X s ω))) P)
    (hCStrong : ∀ n, StronglyMeasurable
      (P[(fun η => f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]))
    (hTStrong : ∀ n, StronglyMeasurable
      (fun ω => ∫ η, f (Sn n ω + X.X (t - s) η) ∂P))
    (hC0Strong : StronglyMeasurable
      (P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]))
    (hT0Strong : StronglyMeasurable
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P))
    (hCDiff : ∀ n, Integrable (fun ω =>
      (P[(fun η => f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
      (P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω) P)
    (hTDiff : ∀ n, Integrable (fun ω =>
      (∫ η, f (Sn n ω + X.X (t - s) η) ∂P) -
      (∫ η, f (Z ω + X.X (t - s) η) ∂P)) P)
    (hDom : ∀ n, Integrable
      (fun ω => L * |Sn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Sn n ω - Z ω| ∂P)
      atTop (nhds 0)) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by
  have hCLim :=
    levy_condExp_lipschitz_L1_approximation_stability
      X s t f L hLip Z (fun n ω => Sn n ω)
      hZ hZn hDom hlim
  have hTLim :=
    levy_transition_random_reserve_L1_continuity
      X (t - s) f L hL hLip hInt (fun n ω => Sn n ω) Z
      (fun n => (hTDiff n).abs) hDom hlim
  exact levy_increment_condExp_general_reserve_of_simple_L1
    X s t hst f hf hInt Sn Z hSn
    hCStrong hTStrong hC0Strong hT0Strong
    hCDiff hTDiff hCLim hTLim

-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:52:12.600378+00:00
-- url     : https://prove2.me/submissions/1608a324-9730-4204-8014-c2e8b3b9eab0

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_condExp_pair_stronglyMeasurable_integrable_difference
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_stronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz

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
    (hZMeas : Measurable Z)
    (hZ : Integrable (fun ω =>
      f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable (fun ω =>
      f (Sn n ω + (X.X t ω - X.X s ω))) P)
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
  have hCE (n : ℕ) :=
    condExp_pair_stronglyMeasurable_integrable_difference
      P (𝓕 s) (𝓕.le s)
      (fun η => f (Sn n η + (X.X t η - X.X s η)))
      (fun η => f (Z η + (X.X t η - X.X s η)))
  have hTM (n : ℕ) :=
    levy_transition_random_reserve_stronglyMeasurable
      X (t - s) f L hL hLip hInt
      (Sn n : Ω → ℝ) (Sn n).measurable
  have hT0 :=
    levy_transition_random_reserve_stronglyMeasurable
      X (t - s) f L hL hLip hInt Z hZMeas
  exact levy_increment_condExp_general_reserve_lipschitz
    X s t hst f hf L hL hLip hInt Sn Z hSn hZ hZn
    (fun n => ((hCE n).1).mono (𝓕.le s)) hTM
    (((hCE 0).2.1).mono (𝓕.le s)) hT0
    (fun n => (hCE n).2.2) hTDiff hDom hlim

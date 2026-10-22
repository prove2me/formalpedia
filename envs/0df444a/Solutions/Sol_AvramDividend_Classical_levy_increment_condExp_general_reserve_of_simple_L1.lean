-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_general_reserve_of_simple_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:02:13.065249+00:00
-- url     : https://prove2.me/submissions/654cd46e-e46d-4aa5-a1c1-6a73d145622a

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_simple_reserve
import Theorems.Thm_AvramDividend_Classical_real_L1_common_ae_limit

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
    (f : ℝ → ℝ) (hf : Measurable f)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Sn : ℕ → SimpleFunc Ω ℝ) (Z : Ω → ℝ)
    (hSn : ∀ n, Measurable[𝓕 s] (Sn n : Ω → ℝ))
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
    (hCLim : Tendsto (fun n : ℕ =>
      ∫ ω, |(P[(fun η =>
          f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η =>
          f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P)
      atTop (nhds 0))
    (hTLim : Tendsto (fun n : ℕ =>
      ∫ ω, |(∫ η, f (Sn n ω + X.X (t - s) η) ∂P) -
        (∫ η, f (Z ω + X.X (t - s) η) ∂P)| ∂P)
      atTop (nhds 0)) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by
  let C (n : ℕ) : Ω → ℝ :=
    P[(fun η => f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]
  let T (n : ℕ) : Ω → ℝ :=
    fun ω => ∫ η, f (Sn n ω + X.X (t - s) η) ∂P
  let C0 : Ω → ℝ :=
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]
  let T0 : Ω → ℝ :=
    fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P
  have hEq (n : ℕ) : C n =ᵐ[P] T n := by
    simpa only [C, T] using
      (levy_increment_condExp_simple_reserve
        X s t hst (Sn n) (hSn n) f hf
        (fun r _ => hInt r))
  exact real_L1_common_ae_limit
    P C T C0 T0 hCStrong hTStrong hC0Strong hT0Strong
    hCDiff hTDiff hEq hCLim hTLim

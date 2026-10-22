-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_random_reserve_L1_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:08:05.541511+00:00
-- url     : https://prove2.me/submissions/75a28809-6564-404a-97dd-fdb843165190

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound

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
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable (fun η => f (u + X.X t η)) P)
    (Zn : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hDiff : ∀ n, Integrable (fun ω =>
      |(∫ η, f (Zn n ω + X.X t η) ∂P) -
        (∫ η, f (Z ω + X.X t η) ∂P)|) P)
    (hDom : ∀ n, Integrable
      (fun ω => L * |Zn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Zn n ω - Z ω| ∂P)
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => ∫ ω,
        |(∫ η, f (Zn n ω + X.X t η) ∂P) -
          (∫ η, f (Z ω + X.X t η) ∂P)| ∂P)
      atTop (nhds 0) := by
  have hNonneg (n : ℕ) :
      0 ≤ ∫ ω,
        |(∫ η, f (Zn n ω + X.X t η) ∂P) -
          (∫ η, f (Z ω + X.X t η) ∂P)| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hUpper (n : ℕ) :
      (∫ ω,
        |(∫ η, f (Zn n ω + X.X t η) ∂P) -
          (∫ η, f (Z ω + X.X t η) ∂P)| ∂P) ≤
      ∫ ω, L * |Zn n ω - Z ω| ∂P := by
    apply integral_mono_ae (hDiff n) (hDom n)
    exact Filter.Eventually.of_forall (fun ω =>
      levy_transition_preserves_lipschitz_bound
        X t f L hL hLip hInt (Zn n ω) (Z ω))
  exact squeeze_zero hNonneg hUpper hlim

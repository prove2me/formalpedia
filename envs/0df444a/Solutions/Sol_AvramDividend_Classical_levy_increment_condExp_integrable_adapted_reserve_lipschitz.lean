-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_integrable_adapted_reserve_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:02:38.358094+00:00
-- url     : https://prove2.me/submissions/6255c485-5a49-4c00-a122-e626e02d333c

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_preserves_adaptedness
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_weighted_real_L1
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_integrable_difference_of_lipschitz
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
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
    (Z : Ω → ℝ)
    (hZ : Measurable[𝓕 s] Z) (hZm : Measurable Z)
    (hZI : Integrable Z P)
    (hZPay : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn Z hZm (Set.range Z ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by
  let S (n : ℕ) : SimpleFunc Ω ℝ :=
    SimpleFunc.approxOn Z hZm (Set.range Z ∪ {0}) 0 (by simp) n
  have hAdapt (n : ℕ) : Measurable[𝓕 s] (S n : Ω → ℝ) :=
    simple_reserve_approxOn_preserves_adaptedness
      (mΩ := mΩ) (𝓕 s) Z hZ hZ
      (Set.range Z ∪ {0}) 0 (by simp) n
  have hSI (n : ℕ) : Integrable (S n : Ω → ℝ) P :=
    SimpleFunc.integrable_approxOn_range hZm hZI n
  have hDom (n : ℕ) :
      Integrable (fun ω => L * |S n ω - Z ω|) P := by
    exact (((hSI n).sub hZI).abs).const_mul L
  have hTLim :=
    simple_reserve_approxOn_weighted_real_L1 P Z hZm hZI L
  have hTDiff (n : ℕ) :
      Integrable (fun ω =>
        (∫ η, f (S n ω + X.X (t - s) η) ∂P) -
        (∫ η, f (Z ω + X.X (t - s) η) ∂P)) P :=
    levy_transition_random_reserve_integrable_difference_of_lipschitz
      X (t - s) f L hL hLip hInt (S n : Ω → ℝ) Z
      (S n).measurable hZm (hDom n)
  exact levy_increment_condExp_general_reserve_lipschitz_measurable
    X s t hst f hf L hL hLip hInt S Z hAdapt hZm
    hZPay (fun n => hSPay n) hTDiff hDom hTLim

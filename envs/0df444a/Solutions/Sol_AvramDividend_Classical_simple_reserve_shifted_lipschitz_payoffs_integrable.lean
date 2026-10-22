-- Prove2me | solution 1 for AvramDividend.Classical.simple_reserve_shifted_lipschitz_payoffs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:42:08.972994+00:00
-- url     : https://prove2.me/submissions/8e435e38-7014-4d78-8235-38c2117d4623

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_lipschitz_shifted_payoff_integrable_of_L1_difference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ → ℝ) (hf : Measurable f)
    (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z Y : Ω → ℝ)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hZI : Integrable Z P)
    (hBase : Integrable (fun ω => f (Z ω + Y ω)) P) :
    ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0
        (by simp) n) ω + Y ω)) P := by
  intro n
  let S : SimpleFunc Ω ℝ :=
    SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0 (by simp) n
  have hSm : Measurable (S : Ω → ℝ) := S.measurable
  have hSi : Integrable (S : Ω → ℝ) P := by
    dsimp [S]
    exact SimpleFunc.integrable_approxOn_range hZ hZI n
  have hDom : Integrable (fun ω => L * |S ω - Z ω|) P :=
    (((hSi.sub hZI).abs).const_mul L)
  exact lipschitz_shifted_payoff_integrable_of_L1_difference
    P f hf L hLip (S : Ω → ℝ) Z Y
    hSm hZ hY hBase hDom

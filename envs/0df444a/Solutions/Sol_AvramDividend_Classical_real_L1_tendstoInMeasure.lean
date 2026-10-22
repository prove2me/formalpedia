-- Prove2me | solution 1 for AvramDividend.Classical.real_L1_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:03:32.23717+00:00
-- url     : https://prove2.me/submissions/f707b2da-b2cb-47b9-afb8-94202101959e

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn : ℕ → Ω → ℝ) (F : Ω → ℝ)
    (hFn : ∀ n, StronglyMeasurable (Fn n))
    (hF : StronglyMeasurable F)
    (hInt : ∀ n, Integrable (fun ω => Fn n ω - F ω) P)
    (hlim : Tendsto
      (fun n : ℕ => ∫ ω, |Fn n ω - F ω| ∂P)
      atTop (nhds 0)) :
    TendstoInMeasure P Fn atTop F := by
  have hENN :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (∫ ω, |Fn n ω - F ω| ∂P))
        atTop (nhds (0 : ENNReal)) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hlim
  have hEq (n : ℕ) :
      eLpNorm (Fn n - F) 1 P =
        ENNReal.ofReal (∫ ω, |Fn n ω - F ω| ∂P) := by
    calc
      eLpNorm (Fn n - F) 1 P =
          ∫⁻ ω, ‖(Fn n - F) ω‖ₑ ∂P :=
        eLpNorm_one_eq_lintegral_enorm
      _ = ENNReal.ofReal
          (∫ ω, ‖(Fn n - F) ω‖ ∂P) :=
        (ofReal_integral_norm_eq_lintegral_enorm (hInt n)).symm
      _ = ENNReal.ofReal
          (∫ ω, |Fn n ω - F ω| ∂P) := by
        simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hNorm :
      Tendsto (fun n : ℕ => eLpNorm (Fn n - F) 1 P)
        atTop (nhds (0 : ENNReal)) := by
    have hFun : (fun n : ℕ => eLpNorm (Fn n - F) 1 P) =
        (fun n : ℕ => ENNReal.ofReal
          (∫ ω, |Fn n ω - F ω| ∂P)) :=
      funext hEq
    rw [hFun]
    exact hENN
  exact tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    (by norm_num : (1 : ENNReal) ≠ 0)
    (by norm_num : (1 : ENNReal) ≠ ∞)
    hFn hF hNorm

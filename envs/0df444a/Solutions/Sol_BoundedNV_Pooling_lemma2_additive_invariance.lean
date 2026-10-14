-- Prove2me | solution 1 for BoundedNV.Pooling.lemma2_additive_invariance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:53:34.822797+00:00
-- url     : https://prove2.me/submissions/0ce147dd-bb17-4b8b-97db-688d20df45bd

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Logit

open MeasureTheory


namespace BoundedNV.Pooling

theorem l2_core (Y : Set ℝ) (u : ℝ → ℝ) (β a : ℝ) (y : ℝ) :
    logitCDF Y (fun v => u v + a) β y = logitCDF Y u β y := by
  unfold logitCDF
  congr 1
  funext w
  unfold logitDensity
  have h1 : ∀ v, Real.exp ((u v + a) / β) = Real.exp (u v / β) * Real.exp (a / β) := by
    intro v; rw [← Real.exp_add]; congr 1; ring
  simp only [h1]
  rw [integral_mul_const]
  by_cases hw : w ∈ Y
  · simp only [Set.indicator_of_mem hw]
    have : Real.exp (a / β) ≠ 0 := (Real.exp_pos _).ne'
    rw [mul_div_mul_right _ _ this]
  · simp [Set.indicator_of_notMem hw]

end BoundedNV.Pooling

open BoundedNV.Pooling
open MeasureTheory

theorem solution (Y : Set ℝ) (u : ℝ → ℝ) (β a : ℝ)
    (hY : MeasurableSet Y)
    (hu : IntegrableOn (fun v => Real.exp (u v / β)) Y)
    (hZ : 0 < ∫ v in Y, Real.exp (u v / β))
    (hβ : 0 < β) (y : ℝ) :
    logitCDF Y (fun v => u v + a) β y = logitCDF Y u β y := by
  exact l2_core Y u β a y

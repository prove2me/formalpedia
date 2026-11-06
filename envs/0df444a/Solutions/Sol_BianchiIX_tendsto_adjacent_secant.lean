-- Prove2me | solution 1 for BianchiIX.tendsto_adjacent_secant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:30:46.249368+00:00
-- url     : https://prove2.me/submissions/1191a57f-fd22-4c31-b476-78fae1941ea6

import Definitions.Def_BianchiIX_Analysis_CurveMeasurability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology


/-- Adjacent interior samples recover even a one-sided derivative. -/
theorem solution {f : ℝ → ℝ} {d x : ℝ} {S : Set ℝ} {h : ℕ → ℝ}
    (hf : HasDerivWithinAt f d S x) (ht : Tendsto h atTop (𝓝 0))
    (hn : ∀ n, h n ≠ 0) (h₁ : ∀ n, x + h n ∈ S) (h₂ : ∀ n, x + 2 * h n ∈ S) :
    Tendsto (fun n => (f (x + 2 * h n) - f (x + h n)) / h n) atTop (𝓝 d) := by
  have ht₁ : Tendsto (fun n => x + h n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add ht
  have ht₂ : Tendsto (fun n => x + 2 * h n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (ht.const_mul 2)
  have hs₁ : Tendsto (fun n => x + h n) atTop (𝓝[S \ {x}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht₁, Eventually.of_forall fun n => ⟨h₁ n, ?_⟩⟩
    simpa using hn n
  have hs₂ : Tendsto (fun n => x + 2 * h n) atTop (𝓝[S \ {x}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht₂, Eventually.of_forall fun n => ⟨h₂ n, ?_⟩⟩
    simpa using hn n
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hf
  have H := ((hs.comp hs₂).const_mul 2).sub (hs.comp hs₁)
  convert! H using 1
  · ext n
    dsimp only [Function.comp_def]
    rw [slope_def_field, slope_def_field]
    simp only [add_sub_cancel_left]
    field_simp [hn n]
    ring
  · congr 1
    ring

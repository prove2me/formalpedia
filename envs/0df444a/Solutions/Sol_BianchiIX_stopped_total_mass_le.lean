-- Prove2me | solution 1 for BianchiIX.stopped_total_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:21:37.524511+00:00
-- url     : https://prove2.me/submissions/3ac230da-b083-42c2-8588-b4f8d6f185cb

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Theorems.Thm_BianchiIX_stopped_layer_mass_le
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal


theorem solution {ι : ℕ → Type*} [∀ m, Countable (ι m)]
    (a : ∀ m, ι m → ℕ → ℕ+) (H : ∀ m, ι m → ℝ → ℝ) (A : ∀ m, ι m → Set ℝ)
    (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hunique : ∀ m, Function.Injective (fun i => digitPrefix (a m i) m))
    (hA : ∀ m i, MeasurableSet (A m i)) (hAsub : ∀ m i, A m i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ m i, ∀ x ∈ A m i, DifferentiableAt ℝ (H m i) x)
    (hinj : ∀ m i, InjOn (H m i) (A m i)) (hsize : ∀ m i, volume (A m i) ≤ ell m)
    (hbound : ∀ m i, ∀ x ∈ A m i,
      |deriv (H m i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a m i) m)) x|) :
    volume (⋃ m, stoppedLayer (H m) (A m)) ≤
      2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by
  calc
    volume (⋃ m, stoppedLayer (H m) (A m)) ≤ ∑' m, volume (stoppedLayer (H m) (A m)) :=
      measure_iUnion_le _
    _ ≤ ∑' m, 2 * ENNReal.ofReal (Real.exp L) * ell m :=
      ENNReal.tsum_le_tsum (fun m => stopped_layer_mass_le (a m) m (H m) (A m)
        (hunique m) (hA m) (hAsub m) (hH m) (hinj m) (hsize m) (hbound m))
    _ = _ := ENNReal.tsum_mul_left

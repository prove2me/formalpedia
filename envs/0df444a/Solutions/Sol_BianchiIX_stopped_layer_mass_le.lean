-- Prove2me | solution 1 for BianchiIX.stopped_layer_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:18:50.293234+00:00
-- url     : https://prove2.me/submissions/904fa8c9-f608-4d94-a766-c124fc6dd5b3

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Theorems.Thm_BianchiIX_gaussCylinder_prefixes_tsum_le_one
import Theorems.Thm_BianchiIX_stopped_node_mass_le
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


theorem solution {ι : Type*} [Countable ι]
    (a : ι → ℕ → ℕ+) (n : ℕ) (H : ι → ℝ → ℝ) (A : ι → Set ℝ)
    {L : ℝ} {ell : ℝ≥0∞}
    (hunique : Function.Injective (fun i => digitPrefix (a i) n))
    (hA : ∀ i, MeasurableSet (A i)) (hAsub : ∀ i, A i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ i, ∀ x ∈ A i, DifferentiableAt ℝ (H i) x) (hinj : ∀ i, InjOn (H i) (A i))
    (hsize : ∀ i, volume (A i) ≤ ell)
    (hbound : ∀ i, ∀ x ∈ A i,
      |deriv (H i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a i) n)) x|) :
    volume (stoppedLayer H A) ≤ 2 * ENNReal.ofReal (Real.exp L) * ell := by
  calc
    volume (stoppedLayer H A) ≤ ∑' i, volume (H i '' A i) := measure_iUnion_le _
    _ ≤ ∑' i, (2 * ENNReal.ofReal (Real.exp L) * ell) *
        volume (gaussCylinder (digitPrefix (a i) n)) :=
      ENNReal.tsum_le_tsum (fun i => stopped_node_mass_le (a i) n
        (hA i) (hAsub i) (hH i) (hinj i) (hsize i) (hbound i))
    _ = (2 * ENNReal.ofReal (Real.exp L) * ell) *
        ∑' i, volume (gaussCylinder (digitPrefix (a i) n)) := ENNReal.tsum_mul_left
    _ ≤ (2 * ENNReal.ofReal (Real.exp L) * ell) * 1 :=
      mul_le_mul le_rfl (gaussCylinder_prefixes_tsum_le_one a n hunique)
        (by positivity) (by positivity)
    _ = _ := mul_one _

-- Prove2me | solution 1 for BianchiIX.gaussCylinder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:36:16.702429+00:00
-- url     : https://prove2.me/submissions/7a8a1627-27f7-4c5e-a2e8-e16b6a9f3576

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (k : ℕ+) :
    gaussCylinder [(k : ℕ)] = Ioo (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + t) ∧ 1 / ((k : ℝ) + t) < 1 / (k : ℝ)
    constructor
    · exact (one_div_lt_one_div (by linarith) (by linarith [ht.1])).mpr (by linarith [ht.2])
    · exact (one_div_lt_one_div (by linarith [ht.1]) hk).mpr (by linarith [ht.1])
  · intro hx
    have hx0 : 0 < x := (by positivity : 0 < 1 / ((k : ℝ) + 1)).trans hx.1
    refine ⟨1 / x - (k : ℝ), ⟨?_, ?_⟩, ?_⟩
    · have h := (lt_div_iff₀ hk).mp hx.2
      apply sub_pos.mpr
      exact (lt_div_iff₀ hx0).mpr (by nlinarith)
    · have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mp hx.1
      have h' : 1 / x < (k : ℝ) + 1 := (div_lt_iff₀ hx0).mpr (by nlinarith)
      linarith
    · simp [gaussWord, gaussInv]

-- Prove2me | solution 1 for BianchiIX.exists_gaussCylinder_subset
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:59:01.433237+00:00
-- url     : https://prove2.me/submissions/fe2a6dad-1b34-4cb0-9b55-e41ffed30d4d

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussCode_prefix
import Theorems.Thm_BianchiIX_gaussWord_diameter
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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

end
end

theorem solution {O : Set ℝ} (hO : IsOpen O)
    (a : ℕ → ℕ+) (ha : gaussCode a ∈ O) :
    ∃ n, gaussCylinder (digitPrefix a (n + 1)) ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (gaussCode a) ha
  have hlim := gauss_diameter_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).2 ε hε).exists
  refine ⟨n, fun x hx => hball ?_⟩
  rcases hx with ⟨t, ht, rfl⟩
  rw [Metric.mem_ball, Real.dist_eq, gaussCode_prefix a (n + 1)]
  exact (gaussWord_diameter _ (digitPrefix_positive a (n + 1))
    ⟨ht.1.le, ht.2.le⟩ (gaussCode_mem_unit _)).trans_lt
      (by simpa only [digitPrefix_length, Function.comp_def] using hn)

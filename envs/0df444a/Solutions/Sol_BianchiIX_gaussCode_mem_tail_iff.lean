-- Prove2me | solution 1 for BianchiIX.gaussCode_mem_tail_iff
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:40:42.875833+00:00
-- url     : https://prove2.me/submissions/1d731d36-8388-491e-af43-2b0993c392c1

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussCode_recurrence
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

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

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

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_pos (a : ℕ → ℕ+) : 0 < gaussCode a := by
  rw [gaussCode_recurrence a]
  apply gaussInv_pos _ (gaussCode_mem_unit (shiftDigits a 1)).1
  exact_mod_cast Nat.succ_le_of_lt (a 0).pos

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_lt_one (a : ℕ → ℕ+) : gaussCode a < 1 := by
  rw [gaussCode_recurrence a]
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have ht := gaussCode_pos (shiftDigits a 1)
  unfold gaussInv
  exact (div_lt_one (by positivity)).mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_reciprocal (a : ℕ → ℕ+) :
    1 / gaussCode a = (a 0 : ℝ) + gaussCode (shiftDigits a 1) := by
  rw [gaussCode_recurrence a]
  simp only [gaussInv, one_div_one_div]

end
end

theorem solution (a : ℕ → ℕ+) (k : ℕ+) :
    gaussCode a ∈ Ioo (0 : ℝ) (1 / (k : ℝ)) ↔ (k : ℕ) ≤ a 0 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast k.pos
  have hrec : gaussCode a < 1 / (k : ℝ) ↔ (k : ℝ) < 1 / gaussCode a := by
    rw [lt_div_iff₀ hk, lt_div_iff₀ (gaussCode_pos a), mul_comm]
  rw [mem_Ioo, and_iff_right (gaussCode_pos a), hrec, gaussCode_reciprocal]
  constructor
  · intro h
    by_contra hn
    have hle : ((a 0 : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hn)
    linarith [gaussCode_lt_one (shiftDigits a 1)]
  · intro h
    have hle : (k : ℝ) ≤ a 0 := by exact_mod_cast h
    linarith [gaussCode_pos (shiftDigits a 1)]

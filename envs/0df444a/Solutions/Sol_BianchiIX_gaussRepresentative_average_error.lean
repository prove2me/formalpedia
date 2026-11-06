-- Prove2me | solution 1 for BianchiIX.gaussRepresentative_average_error
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:11:49.17182+00:00
-- url     : https://prove2.me/submissions/a2a6efd6-7e99-4c72-b84f-d7b48ea4e994

import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_empiricalMass_weighted_hasSum
import Theorems.Thm_BianchiIX_gaussCode_prefix
import Theorems.Thm_BianchiIX_gaussCode_recurrence
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
import Theorems.Thm_BianchiIX_timeAverage_sub
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates

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
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.gaussCode_mem_cylinder (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a ∈ gaussCylinder (digitPrefix a n) :=
  ⟨gaussCode (shiftDigits a n),
    ⟨gaussCode_pos _, gaussCode_lt_one _⟩, (gaussCode_prefix a n).symm⟩

end
end

private theorem BianchiIX.timeAverage_abs_le {u : ℕ → ℝ} {ε : ℝ} (hu : ∀ j, |u j| ≤ ε)
    (N : ℕ) : |timeAverage u (N + 1)| ≤ ε := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [timeAverage, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), |u j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hN.le)
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ _j ∈ Finset.range (N + 1), ε :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hu j)) (inv_nonneg.mpr hN.le)
    _ = ε := by simp [show (N : ℝ) + 1 ≠ 0 by positivity]

theorem solution (a : ℕ → ℕ+) {f : ℝ → ℝ} (n N : ℕ) {ε : ℝ}
    (hosc : ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε) :
    |timeAverage (fun j => f (gaussMap^[j] (gaussCode a))) (N + 1) -
      ∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w)| ≤ ε := by
  simp only [gaussEmpiricalMass]
  rw [(empiricalMass_weighted_hasSum
    (fun j => gaussPrefixWord (shiftDigits a j) n) N (fun w => f (gaussRepresentative n w))).tsum_eq]
  change |timeAverage _ (N + 1) - timeAverage _ (N + 1)| ≤ ε
  rw [← timeAverage_sub]
  apply timeAverage_abs_le
  intro j
  rw [gaussMap_iterate_code]
  exact hosc (gaussPrefixWord (shiftDigits a j) n) _ (gaussCode_mem_cylinder (shiftDigits a j) n)

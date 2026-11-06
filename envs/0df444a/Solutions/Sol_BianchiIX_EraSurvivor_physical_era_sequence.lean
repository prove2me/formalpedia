-- Prove2me | solution 1 for BianchiIX.EraSurvivor.physical_era_sequence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:34:14.841145+00:00
-- url     : https://prove2.me/submissions/00326718-267d-467d-983d-9e45df0ca8ac

import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Theorems.Thm_BianchiIX_gauss_truncated_integral_tendsto_atTop
import Theorems.Thm_BianchiIX_timeAverage_tendsto_atTop_of_truncations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.shiftDigits_add (a : ℕ → ℕ+) (m n : ℕ) :
    shiftDigits (shiftDigits a m) n = shiftDigits a (m + n) := by
  funext i
  simp only [shiftDigits, Nat.add_assoc]

end
end

section
open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

private theorem BianchiIX.timeAverage_shift (u : ℕ → ℝ) (k n : ℕ) (hn : 0 < n) :
    timeAverage (fun j => u (k + j)) n =
      (1 + (k : ℝ) * (n : ℝ)⁻¹) * timeAverage u (k + n) -
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkn0 : ((k + n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.add_pos_right k hn).ne'
  simp only [timeAverage, Finset.sum_range_add]
  field_simp
  push_cast
  ring

end

section
open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

private theorem BianchiIX.timeAverage_shift_tendsto_iff (u : ℕ → ℝ) (k : ℕ) (l : ℝ) :
    Tendsto (timeAverage (fun j => u (k + j))) atTop (𝓝 l) ↔
      Tendsto (timeAverage u) atTop (𝓝 l) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hf : Tendsto (fun n : ℕ => 1 + (k : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
  have hp : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) atTop (𝓝 0) := by
    simpa using hi.mul tendsto_const_nhds
  have hindex : Tendsto (fun n : ℕ => k + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k
  constructor
  · intro h
    have hlim := (h.add hp).div hf (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun n : ℕ =>
        (timeAverage (fun j => u (k + j)) n + (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) /
          (1 + (k : ℝ) * (n : ℝ)⁻¹)) =ᶠ[atTop] (fun n => timeAverage u (k + n)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hf0 : 1 + (k : ℝ) * (n : ℝ)⁻¹ ≠ 0 := by positivity
      rw [timeAverage_shift u k n hn, sub_add_cancel]
      exact mul_div_cancel_left₀ _ hf0
    have hs : Tendsto (fun n => timeAverage u (n + k)) atTop (𝓝 l) := by
      simpa only [add_zero, div_one, Nat.add_comm] using hlim.congr' heq
    exact (tendsto_add_atTop_iff_nat k).mp hs
  · intro h
    have hlim := (hf.mul (h.comp hindex)).sub hp
    have heq : (fun n : ℕ =>
        (1 + (k : ℝ) * (n : ℝ)⁻¹) * timeAverage u (k + n) -
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range k, u j) =ᶠ[atTop]
        timeAverage (fun j => u (k + j)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (timeAverage_shift u k n hn).symm
    simpa only [one_mul, sub_zero] using hlim.congr' heq

end

section
open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

private theorem BianchiIX.eraStatistics_shift_iff (a : ℕ → ℕ+) (y : ℕ → ℝ) (k : ℕ) :
    EraStatistics (shiftDigits a k) (fun j => y (k + j)) ↔ EraStatistics a y := by
  constructor
  · intro h
    have ht (R : ℕ) := (timeAverage_shift_tendsto_iff
      (fun j => min (a j : ℝ) (R : ℝ)) k _).mp (h.truncated_average R)
    refine ⟨?_, ?_, ?_, ?_, ht,
      timeAverage_tendsto_atTop_of_truncations ht gauss_truncated_integral_tendsto_atTop⟩
    · intro f hf
      exact (timeAverage_shift_tendsto_iff (fun j => f (y j)) k _).mp (h.continuous_average f hf)
    · intro w hw
      apply (timeAverage_shift_tendsto_iff
        (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0) k _).mp
      simpa only [shiftDigits_add] using h.block_frequency w hw
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (a j : ℕ) = (r : ℕ) then 1 else 0) k _).mp
        (h.digit_frequency r)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (r : ℕ) ≤ (a j : ℕ) then 1 else 0) k _).mp
        (h.tail_frequency r)
  · intro h
    have ht (R : ℕ) := (timeAverage_shift_tendsto_iff
      (fun j => min (a j : ℝ) (R : ℝ)) k _).mpr (h.truncated_average R)
    refine ⟨?_, ?_, ?_, ?_, ht,
      timeAverage_tendsto_atTop_of_truncations ht gauss_truncated_integral_tendsto_atTop⟩
    · intro f hf
      exact (timeAverage_shift_tendsto_iff (fun j => f (y j)) k _).mpr (h.continuous_average f hf)
    · intro w hw
      simpa only [shiftDigits_add] using (timeAverage_shift_tendsto_iff
        (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0) k _).mpr
        (h.block_frequency w hw)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (a j : ℕ) = (r : ℕ) then 1 else 0) k _).mpr
        (h.digit_frequency r)
    · intro r
      exact (timeAverage_shift_tendsto_iff (fun j => if (r : ℕ) ≤ (a j : ℕ) then 1 else 0) k _).mpr
        (h.tail_frequency r)

end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_shears (x : NormalizedState) :
    normalizedShears (axisCycle x) = ![normalizedShears x 1, normalizedShears x 2, normalizedShears x 0] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_shears (x : NormalizedState) :
    normalizedShears (axisSwap x) = ![normalizedShears x 0, normalizedShears x 2, normalizedShears x 1] := by
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisSwap] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisOrder_bijective : ∀ i, Function.Bijective (axisOrder i) := by decide

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_walls (i : Fin 6) (x : NormalizedState) :
    normalizedWalls ((axisFrame i).map x) = fun j => normalizedWalls x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_shears (i : Fin 6) (x : NormalizedState) :
    normalizedShears ((axisFrame i).map x) = fun j => normalizedShears x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i
  · ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle x) = _
    rw [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle (axisCycle x)) = _
    simp only [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap x) = _
    rw [axisSwap_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle x)) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle (axisCycle x))) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedState_ext_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) : x = y := by
  have h₀ := congrFun hs 0
  have h₁ := congrFun hs 1
  change -2 * x 0 = -2 * y 0 at h₀
  change x 0 - Real.sqrt 3 * x 1 = y 0 - Real.sqrt 3 * y 1 at h₁
  have hx₀ : x 0 = y 0 := by linarith
  have hx₁ : x 1 = y 1 := mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    (by linarith : Real.sqrt 3 * x 1 = Real.sqrt 3 * y 1)
  ext i
  fin_cases i
  · exact hx₀
  · exact hx₁
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_comp (i j : Fin 6) :
    ∃ k : Fin 6, ∀ x : NormalizedState,
      (axisFrame i).map ((axisFrame j).map x) = (axisFrame k).map x := by
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder i) (axisOrder_bijective i)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder j) (axisOrder_bijective j)
  obtain ⟨k, hk⟩ := axisOrder_covers (σ.trans τ)
  refine ⟨k, fun x => normalizedState_ext_shears_walls ?_ ?_⟩
  · ext l
    simp only [axisFrame_shears, hk]
    rfl
  · ext l
    simp only [axisFrame_walls, hk]
    rfl

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.elapsedTime_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    elapsedTime p (n + 1) = duration p n + elapsedTime p n := by
  rw [elapsedTime, Finset.sum_range_succ]
  exact add_comm _ _

end
end

section
noncomputable section
open BianchiIX
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.frame_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) (x : NormalizedState) :
    (axisFrame (frame p (n + 1))).map x =
      (axisFrame (eraReturnFrame (digits p n).natPred)).map ((axisFrame (frame p n)).map x) :=
  ((axisFrame_comp (eraReturnFrame (digits p n).natPred) (frame p n)).choose_spec x).symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.physicalTime_succ (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    physicalTime w p (n + 1) = duration p n + physicalTime w p n := by
  simp only [physicalTime, elapsedTime_succ, add_assoc]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.physicalFrame_succ (w : CoreRestartData) (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) (z : NormalizedState) :
    (axisFrame (physicalFrame w p (n + 1))).map z =
      (axisFrame (eraReturnFrame (digits p n).natPred)).map ((axisFrame (physicalFrame w p n)).map z) := by
  rw [physicalFrame, ← (axisFrame_comp (frame p (n + 1)) w.1.1).choose_spec, frame_succ,
    (axisFrame_comp (frame p n) w.1.1).choose_spec]
  rfl

end
end

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}



/-- Removing the initial block leaves complete eras with the same full statistics and an actual preceding terminal connection. -/
theorem solution {x : NormalizedState} (w : CoreRestartData)
    (p : eraSurvivorDomain η J σ Bcap) (hc : stateConstraint x = 1)
    (Hstat : EraStatistics (digits p) (phase p))
    (Hblocks : ∀ n, EraEventItinerary η J (digits p n).natPred (state p n) ∧
      coreRadiusEntry (state p (n + 1)) = terminalNaturalState η J (eraCoreExit (digits p n).natPred (state p n)))
    (Hmono : StrictMono (physicalTime w p))
    (Htop : Tendsto (physicalTime w p) atTop atTop)
    (Hactual : ∀ n, 0 < physicalTime w p n ∧
      fromProjectiveState (coreRadiusEntry (state p n)) =
        (axisFrame (physicalFrame w p n)).map (normalizedMaxCurve x 0 (physicalTime w p n))) :
    PhysicalEraSequence η J x (fun n => digits p (n + 1)) (fun n => state p (n + 1))
      (fun n => physicalTime w p (n + 1)) (fun n => physicalFrame w p (n + 1)) := by
  refine ⟨hc, ?_, fun n => (Hactual (n + 1)).1, ?_, ?_, fun n => (Hactual (n + 1)).2,
    fun n => (Hblocks (n + 1)).1, fun n => (Hblocks (n + 1)).2,
    fun n => physicalTime_succ w p (n + 1), fun n z => physicalFrame_succ w p (n + 1) z, ?_⟩
  · have HT := (eraStatistics_shift_iff (digits p) (phase p) 1).mpr Hstat
    change EraStatistics (fun n => digits p (1 + n)) (fun n => 2 / state p (1 + n) 0) at HT
    simpa only [Nat.add_comm 1] using HT
  · exact fun i j hij => Hmono (Nat.add_lt_add_right hij 1)
  · exact Htop.comp (tendsto_add_atTop_nat 1)
  · exact ⟨(digits p 0).natPred, state p 0, physicalTime w p 0, physicalFrame w p 0,
      (Hblocks 0).1, (Hactual 0).1, Hmono (by omega), (Hactual 0).2,
      physicalTime_succ w p 0, (Hblocks 0).2, fun z => physicalFrame_succ w p 0 z⟩

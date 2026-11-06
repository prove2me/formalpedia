-- Prove2me | solution 1 for BianchiIX.exists_common_borel_era_orbit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:21:57.783847+00:00
-- url     : https://prove2.me/submissions/f4fcb5b6-151c-4891-adb5-4ab81fc25c85

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_CoreRestartWitness_exists_measurable_survivor
import Theorems.Thm_BianchiIX_CoreRestartWitness_physical_orbit
import Theorems.Thm_BianchiIX_CoreRestartWitness_restrict_cap
import Theorems.Thm_BianchiIX_EraSurvivor_phase_measurable
import Theorems.Thm_BianchiIX_EraSurvivor_physicalFrame_measurable
import Theorems.Thm_BianchiIX_EraSurvivor_physicalTime_measurable
import Theorems.Thm_BianchiIX_EraSurvivor_state_measurable
import Theorems.Thm_BianchiIX_exists_common_borel_core_restart
import Theorems.Thm_BianchiIX_exists_era_input_time_regular
import Theorems.Thm_BianchiIX_exists_era_output_estimates
import Theorems.Thm_BianchiIX_exists_era_survivor_events
import Theorems.Thm_BianchiIX_exists_era_survivor_unbounded_orbit
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_gauss_truncated_integral_tendsto_atTop
import Theorems.Thm_BianchiIX_measurable_gaussCode
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Interval.Set.Monotone

noncomputable section
open BianchiIX
open Set MeasureTheory Filter
open scoped Topology

section
open BianchiIX
open Set

private theorem BianchiIX.measurable_comp_of_continuousAt {X Y Z : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {g : X → Y} {f : Y → Z} (hg : Measurable g)
    (hf : ∀ x, ContinuousAt f (g x)) : Measurable (f ∘ g) := by
  have hc : ContinuousOn f (range g) := by
    rintro _ ⟨x, rfl⟩
    exact (hf x).continuousWithinAt
  have hg' : Measurable (fun x => (⟨g x, mem_range_self x⟩ : range g)) := hg.subtype_mk
  exact hc.domRestrict.measurable.comp hg'

end

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
open Set

private theorem BianchiIX.measurableSet_eraInputSelection {σ : ℝ} (hσ : 0 ≤ σ) (Bstar : ℝ) (m : ℕ) :
    MeasurableSet (eraInputSelection σ Bstar m) := by
  have hβ : Measurable (fun p : ℝ × CoreAngleState => p.1 ^ σ) :=
    (Real.continuous_rpow_const hσ).measurable.comp measurable_fst
  have hx (i : Fin 3) : Measurable (fun p : ℝ × CoreAngleState => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const (measurable_const.div hβ).nat_floor).inter
      ((measurableSet_lt measurable_const (hx 1)).inter
        ((measurableSet_lt measurable_const (hx 2)).inter
          ((measurableSet_le ((hx 1).add (hx 2)) measurable_fst).inter
            ((measurableSet_le ((measurable_const.add hβ).const_mul 2) (hx 0)).inter
              (measurableSet_le (hx 0) ((measurable_const.sub hβ).const_mul 2)))))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraInputSelection_disjoint {σ Bstar : ℝ} {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (eraInputSelection σ Bstar m) (eraInputSelection σ Bstar n) := by
  apply disjoint_left.mpr
  intro p hm hn
  have hβ : 0 < p.1 ^ σ := Real.rpow_pos_of_pos hm.1.1 _
  have hrm := hm.2.2.2.2.2
  have hrn := hn.2.2.2.2.2
  rcases lt_or_gt_of_ne hmn with h | h
  · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hrm.2, hrn.1]
  · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hrn.2, hrm.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraSelectedInputs_disjoint (η : ℝ) (J : ℕ) (σ Bstar : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (eraSelectedInputs η J σ Bstar m) (eraSelectedInputs η J σ Bstar n) :=
  (eraInputSelection_disjoint hmn).mono (fun _ h => h.1) (fun _ h => h.1)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraSelectedInputs_measurable_of_contDiff {η σ Bstar : ℝ} {J m : ℕ} (hσ : 0 ≤ σ)
    (H : ∀ p ∈ eraInputSelection σ Bstar m, ContDiffAt ℝ 1 (eraNextState η J m) p.2) :
    MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val) := by
  let D := eraInputSelection σ Bstar m
  have hD : MeasurableSet D := measurableSet_eraInputSelection hσ Bstar m
  have hstate : Measurable (fun p : D => eraNextState η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (H p.val p.property).continuousAt)
  have hphase : Measurable (fun p : D => 2 / eraOutputRadius η J m p.val.2) :=
    measurable_const.div ((measurable_pi_apply 0).comp hstate)
  have hβ : Measurable (fun p : D => p.val.1 ^ σ) :=
    (Real.continuous_rpow_const hσ).measurable.comp (measurable_fst.comp measurable_subtype_coe)
  have hs : MeasurableSet {p : D | 2 / eraOutputRadius η J m p.val.2 ∈
      Ioo (2 * p.val.1 ^ σ) (1 - 2 * p.val.1 ^ σ)} :=
    (measurableSet_lt (hβ.const_mul 2) hphase).inter
      (measurableSet_lt hphase (measurable_const.sub (hβ.const_mul 2)))
  have heq : eraSelectedInputs η J σ Bstar m =
      Subtype.val '' {p : D | 2 / eraOutputRadius η J m p.val.2 ∈
        Ioo (2 * p.val.1 ^ σ) (1 - 2 * p.val.1 ^ σ)} := by
    ext p
    constructor
    · exact fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
  refine ⟨by rw [heq]; exact hD.subtype_image hs, ?_⟩
  have hnext : Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraNextState η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (H p.val p.property.1).continuousAt)
  change Measurable (fun p : eraSelectedInputs η J σ Bstar m =>
    (p.val.1 ^ (4 / 3 : ℝ), eraNextState η J m p.val.2))
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4 / 3)).measurable.comp
    (measurable_fst.comp measurable_subtype_coe)).prodMk hnext

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_era_selected_inputs_measurable :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ,
          (∀ p ∈ eraInputSelection σ Bstar m, ContDiffAt ℝ 1 (eraNextState η J m) p.2) ∧
          MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
          Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_output_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, Hout⟩ := Hδ η hη hηδ J hJ
  obtain ⟨Bs, hBs, hBsone, Hbudget⟩ :=
    exists_retained_era_parameter_budget hε (by linarith : 0 ≤ C) hσ hσone hσJ
  refine ⟨Bs, hBs, hBsone, ?_⟩
  intro m
  have Hactual : ∀ p ∈ eraInputSelection σ Bs m, ContDiffAt ℝ 1 (eraNextState η J m) p.2 := by
    intro p hp
    obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
    obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hbudget p.1 hB
    have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
      (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
        (Nat.floor_le (by positivity))
    have hrpos : 0 < p.2 0 := by nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m]
    have hBr : p.1 * p.2 0 ≤ ε :=
      (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
    have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ ε / p.2 0 :=
      (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr)
    obtain ⟨HS, HR, _⟩ := Hout m (p.1 ^ σ) p.2 hβ (by linarith)
      ⟨hu, hwall (by linarith)⟩ ⟨hw, hwall (by linarith)⟩ (hsum.trans hsmall)
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
      ((mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ C)).trans_lt hmargin)
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact HR
    · exact contDiffAt_pi.mp HS 1
    · exact contDiffAt_pi.mp HS 3
  exact ⟨Hactual, eraSelectedInputs_measurable_of_contDiff hσ.le Hactual⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mem_eraPrefixDomain_append (η : ℝ) (J : ℕ) (σ Bstar : ℝ)
    (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    p ∈ eraPrefixDomain η J σ Bstar (v ++ w) ↔
      p ∈ eraPrefixDomain η J σ Bstar v ∧ eraPrefixState η J v p ∈ eraPrefixDomain η J σ Bstar w := by
  induction v generalizing p with
  | nil => simp [eraPrefixDomain, eraPrefixState]
  | cons a v ih =>
    simp only [List.cons_append, eraPrefixDomain, mem_inter_iff, mem_preimage, eraPrefixState,
      Function.comp_apply, ih]
    exact and_assoc.symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixDomain_unique (η : ℝ) (J : ℕ) (σ Bstar : ℝ) {v w : List ℕ+}
    (hlen : v.length = w.length) {p : ℝ × CoreAngleState}
    (hv : p ∈ eraPrefixDomain η J σ Bstar v) (hw : p ∈ eraPrefixDomain η J σ Bstar w) : v = w := by
  induction v generalizing w p with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have hab : a = b := by
        by_contra hne
        have hd := eraSelectedInputs_disjoint η J σ Bstar
          (fun he => hne (PNat.natPred_injective he))
        exact Set.disjoint_left.mp hd hv.1 hw.1
      subst b
      exact congrArg (List.cons a) (ih (Nat.succ.inj hlen) hv.2 hw.2)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val))
    (w : List ℕ+) : MeasurableSet (eraPrefixDomain η J σ Bstar w) ∧
      Measurable (fun p : eraPrefixDomain η J σ Bstar w => eraPrefixState η J w p.val) := by
  induction w with
  | nil => exact ⟨MeasurableSet.univ, measurable_subtype_coe⟩
  | cons a w ih =>
    let S := eraSelectedInputs η J σ Bstar a.natPred
    let D := eraPrefixDomain η J σ Bstar w
    let Q := eraBudgetReturn η J a.natPred
    have hA : MeasurableSet {p : S | Q p.val ∈ D} := ih.1.preimage (H a.natPred).2
    have heq : eraPrefixDomain η J σ Bstar (a :: w) = Subtype.val '' {p : S | Q p.val ∈ D} := by
      ext p
      constructor
      · exact fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.property, hp⟩
    refine ⟨by rw [heq]; exact (H a.natPred).1.subtype_image hA, ?_⟩
    have hi : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨p.val, p.property.1⟩ : S)) :=
      measurable_subtype_coe.subtype_mk
    have hQ : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => Q p.val) :=
      (H a.natPred).2.comp hi
    have hmap : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨Q p.val, p.property.2⟩ : D)) :=
      hQ.subtype_mk
    exact ih.2.comp hmap

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.word_eq_iff (p : eraSurvivorDomain η J σ Bstar) {n : ℕ} {w : List ℕ+} (hw : w.length = n) :
    word p n = w ↔ p.val ∈ eraPrefixDomain η J σ Bstar w := by
  constructor
  · exact fun h => h ▸ mem_word_domain p n
  · exact fun h => eraPrefixDomain_unique η J σ Bstar ((word_length p n).trans hw.symm) (mem_word_domain p n) h

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.exists_next_digit (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    ∃ a : ℕ+, word p (n + 1) = word p n ++ [a] := by
  have hl := word_length p (n + 1)
  have hp := mem_word_domain p (n + 1)
  generalize word p (n + 1) = w at hl hp ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = word p n := eraPrefixDomain_unique η J σ Bstar
      (by simpa [word_length] using hl)
      ((mem_eraPrefixDomain_append η J σ Bstar w [a] p.val).mp hp).1 (mem_word_domain p n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.word_succ (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    word p (n + 1) = word p n ++ [digits p n] := (exists_next_digit p n).choose_spec

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.digit_fiber (n : ℕ) (a : ℕ+) :
    {p : eraSurvivorDomain η J σ Bstar | digits p n = a} =
      ⋃ w : {w : List ℕ+ // w.length = n},
        (Subtype.val : eraSurvivorDomain η J σ Bstar → ℝ × CoreAngleState) ⁻¹'
          eraPrefixDomain η J σ Bstar (w.val ++ [a]) := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · intro h
    refine ⟨⟨word p n, word_length p n⟩, ?_⟩
    simpa only [word_succ, h] using mem_word_domain p (n + 1)
  · rintro ⟨⟨w, hw⟩, hp⟩
    have heq := (word_eq_iff p (by simp [hw] : (w ++ [a]).length = n + 1)).mpr hp
    rw [word_succ] at heq
    exact List.singleton_inj.mp (List.append_inj_right heq ((word_length p n).trans hw.symm))

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.digits_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (digits (η := η) (J := J) (σ := σ) (Bstar := Bstar)) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro a
  change MeasurableSet {p : eraSurvivorDomain η J σ Bstar | digits p n = a}
  rw [digit_fiber]
  exact MeasurableSet.iUnion (fun w =>
    ((eraPrefixDomain_measurable H (w.val ++ [a])).1).preimage measurable_subtype_coe)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.code_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (code (η := η) (J := J) (σ := σ) (Bstar := Bstar)) :=
  measurable_gaussCode.comp (digits_measurable H)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_common_borel_era_coding
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ Bbound : ℝ, 0 < Bbound → ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ Bcap ≤ Bbound ∧
          (∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
            Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val)) ∧
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              (∀ x ∈ physicalPhaseSpace, x ∉ N → CoreRestartWitness η J σ Bcap x (W x)) ∧
              ∃ p : ↥(physicalPhaseSpace \ N) → eraSurvivorDomain η J σ Bcap,
                Measurable p ∧ Measurable (EraSurvivor.digits ∘ p) ∧
                Measurable (EraSurvivor.code ∘ p) ∧ Measurable (EraSurvivor.state ∘ p) ∧
                Measurable (EraSurvivor.phase ∘ p) ∧
                ∀ x, (p x).val = (W x.val).2 ∧
                  EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) := by
  obtain ⟨δG, hδG, hδmax, HG⟩ := exists_common_borel_core_restart hBirkhoff hBrehm
  obtain ⟨δM, hδM, _, HM⟩ := exists_era_selected_inputs_measurable
  refine ⟨min δG δM, lt_min hδG hδM, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ Bbound hBbound
  obtain ⟨_, _, _, HB⟩ := HG η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BM, hBM, hBMone, Hinputs⟩ :=
    HM η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  let Bcap := min BM Bbound
  have hcap : 0 < Bcap := lt_min hBM hBbound
  have hcapone : Bcap < 1 := (min_le_left _ _).trans_lt hBMone
  have Hmeas (m : ℕ) := eraSelectedInputs_measurable_of_contDiff (η := η) (J := J) (Bstar := Bcap) hσ.le
    (fun p hp => (Hinputs m).1 p ⟨⟨hp.1.1, hp.1.2.trans (min_le_left _ _)⟩, hp.2⟩)
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, W, hW, HWB⟩ := HB Bcap hcap
  have HW (x : NormalizedState) (hx : x ∈ physicalPhaseSpace) (hn : x ∉ N) :
      CoreRestartWitness η J σ Bcap x (W x) := by
    obtain ⟨hB, H⟩ := HWB x hx hn
    exact H.restrict_cap (hB.trans hcapone.le) hB
  obtain ⟨p, hpm, Hp⟩ := CoreRestartWitness.exists_measurable_survivor
    (S := physicalPhaseSpace \ N) (C := id) hW (fun x hx => HW x hx.1 hx.2)
  exact ⟨Bcap, hcap, hcapone, min_le_right _ _, Hmeas, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, HW, p, hpm, (EraSurvivor.digits_measurable Hmeas).comp hpm,
    (EraSurvivor.code_measurable Hmeas).comp hpm, (EraSurvivor.state_measurable Hmeas).comp hpm,
    (EraSurvivor.phase_measurable Hmeas).comp hpm, Hp⟩

end
end

/-- On one invariant null exception's complement, the jointly Borel selected sequence is an exact orbit with unbounded original arrival times. -/
theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              ∃ p : ↥(physicalPhaseSpace \ N) → eraSurvivorDomain η J σ Bcap,
                Measurable p ∧ Measurable (EraSurvivor.digits ∘ p) ∧
                Measurable (EraSurvivor.code ∘ p) ∧ Measurable (EraSurvivor.state ∘ p) ∧
                Measurable (EraSurvivor.phase ∘ p) ∧
                Measurable (fun x => EraSurvivor.physicalTime (W x.val) (p x)) ∧
                Measurable (fun x => EraSurvivor.physicalFrame (W x.val) (p x)) ∧ ∀ x,
                  (p x).val = (W x.val).2 ∧ EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) ∧
                  EraStatistics (shiftDigits (EraSurvivor.digits (p x)) 1)
                    (fun n => EraSurvivor.phase (p x) (1 + n)) ∧
                  (∀ n, Nat.floor (EraSurvivor.state (p x) n 0 / 2) = (EraSurvivor.digits (p x) n : ℕ)) ∧
                  StrictMono (EraSurvivor.physicalTime (W x.val) (p x)) ∧
                  Tendsto (EraSurvivor.physicalTime (W x.val) (p x)) atTop atTop ∧ ∀ n,
                    EraEventItinerary η J (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n) ∧
                    coreRadiusEntry (EraSurvivor.state (p x) (n + 1)) = terminalNaturalState η J
                      (eraCoreExit (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n)) ∧
                    0 < EraSurvivor.physicalTime (W x.val) (p x) n ∧
                    EraSurvivor.physicalTime (W x.val) (p x) n ∈ normalizedMaxDomain x.val 0 ∧
                    fromProjectiveState (coreRadiusEntry (EraSurvivor.state (p x) n)) =
                      (axisFrame (EraSurvivor.physicalFrame (W x.val) (p x) n)).map
                        (normalizedMaxCurve x.val 0 (EraSurvivor.physicalTime (W x.val) (p x) n)) := by
  obtain ⟨δC, hδC, hδmax, HC⟩ := exists_common_borel_era_coding hBirkhoff hBrehm
  obtain ⟨δO, hδO, _, HO⟩ := exists_era_survivor_unbounded_orbit
  obtain ⟨δT, hδT, _, HT⟩ := exists_era_input_time_regular
  obtain ⟨δE, hδE, _, HE⟩ := exists_era_survivor_events
  refine ⟨min δC (min δO (min δT δE)), lt_min hδC (lt_min hδO (lt_min hδT hδE)),
    (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  have hδOT := hηδ.trans (min_le_right _ _)
  have hδTE := hδOT.trans (min_le_right _ _)
  obtain ⟨BO, hBO, _, Hphys⟩ := HO η hη (hδOT.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BT, hBT, _, Htime⟩ := HT η hη (hδTE.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BE, hBE, _, Hevents⟩ := HE η hη (hδTE.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hcapOT, Hmeas, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, HW, p, hpm, had, hac, has, hap, Hp⟩ :=
    HC η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
      (min BO (min BT BE)) (lt_min hBO (lt_min hBT hBE))
  have hcapTE := hcapOT.trans (min_le_right _ _)
  have Hregular (m : ℕ) (q : ℝ × CoreAngleState) (hq : q ∈ eraSelectedInputs η J σ Bcap m) :
      ContDiffAt ℝ 1 (eraReturnTime η J m) q.2 :=
    Htime Bcap (hcapTE.trans (min_le_left _ _)) m q hq.1
  have hpair : Measurable (fun x : ↥(physicalPhaseSpace \ N) => (W x.val, p x)) :=
    (hW.comp measurable_subtype_coe).prodMk hpm
  refine ⟨Bcap, hcap, hcapone, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, p, hpm, had, hac, has, hap, ?_, ?_, ?_⟩
  · convert (EraSurvivor.physicalTime_measurable Hmeas Hregular).comp hpair using 1
    rfl
  · convert (EraSurvivor.physicalFrame_measurable Hmeas).comp hpair using 1
    rfl
  · intro x
    obtain ⟨hval, hstat⟩ := Hp x
    obtain ⟨Hstep, Hmono, Htop, Horbit⟩ := Hphys Bcap (hcapOT.trans (min_le_left _ _)) (p x)
    have Hx := (HW x.val x.property.1 x.property.2).physical_orbit x.property.1.2 (p x) hval
      Hmono Htop (fun n => (Horbit n).2)
    have Htail := (eraStatistics_shift_iff (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) 1).mpr hstat
    refine ⟨hval, hstat, Htail, fun n => (Hstep n).2.2, Hx.1, Hx.2.1, ?_⟩
    intro n
    obtain ⟨Hblock, Hnext⟩ := Hevents Bcap (hcapTE.trans (min_le_right _ _)) (p x) n
    exact ⟨Hblock, Hnext, Hx.2.2 n⟩

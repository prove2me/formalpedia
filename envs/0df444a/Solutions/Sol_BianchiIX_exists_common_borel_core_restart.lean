-- Prove2me | solution 1 for BianchiIX.exists_common_borel_core_restart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:19:57.086018+00:00
-- url     : https://prove2.me/submissions/a8b61ec6-0c3a-459d-ad4e-d7d571369657

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_PhysicalFutureData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_common_borel_success_exception
import Theorems.Thm_BianchiIX_exists_restartClosedSection_borel_restart
import Theorems.Thm_BianchiIX_exists_smallAxis_borel_first_success
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_mainWallRadicand (h : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (mainWallRadicand h) := by
  unfold mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_mainWallChartDomain (h : ℝ) : IsOpen (mainWallChartDomain h) :=
  isOpen_lt continuous_const (contDiff_mainWallRadicand h 1).continuous

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallCoordinates_chart (h : ℝ) (y : SectionCoordinates) :
    mainWallCoordinates (mainWallChart h y) = y := by
  ext i
  fin_cases i <;> simp [mainWallCoordinates, mainWallChart]

end
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

private theorem BianchiIX.axisPermutation_walls (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    normalizedWalls ((axisPermutation σ).map x) = fun j => normalizedWalls x (σ j) := by
  rw [axisPermutation, axisFrame_walls]
  funext j
  rw [(axisOrder_covers σ).choose_spec j]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallCoordinates_chart (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) :
    axisWallCoordinates A (axisWallChart A h y) = y := by
  simp [axisWallCoordinates, axisWallChart, mainWallCoordinates_chart]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_injective (A : NormalizedSymmetry) (h : ℝ) :
    Function.Injective (axisWallChart A h) :=
  Function.LeftInverse.injective (axisWallCoordinates_chart A h)

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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.axisFamilyMeasure_apply {ι : Type*} [MeasurableSpace ι] (k : ι → ℝ)
    {S : Set (ι × SectionCoordinates)} (hS : MeasurableSet S) :
    axisFamilyMeasure k S = ∑' i, mainWallMeasure (k i) (Prod.mk i ⁻¹' S) := by
  rw [axisFamilyMeasure, Measure.sum_apply _ hS]
  exact tsum_congr (fun _ => Measure.map_apply measurable_prodMk_left hS)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_axisFamilySection {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {E : ι → Set SectionCoordinates}
    (hE : ∀ i, MeasurableSet (E i)) : MeasurableSet (axisFamilySection E) := by
  have heq : axisFamilySection E = ⋃ i, ({i} ×ˢ E i) := by
    ext z
    simp [axisFamilySection]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod (hE i))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisPermutationChart_walls (σ : Equiv.Perm (Fin 3)) (h : ℝ) (y : SectionCoordinates) (j : Fin 3) :
    normalizedWalls (axisWallChart (axisPermutation σ) h y) (σ j) =
      ![h, Real.exp (-y 1), Real.exp (-y 2)] j := by
  have H := congrArg (fun v : Fin 3 → ℝ => v j)
    (axisPermutation_walls σ (axisWallChart (axisPermutation σ) h y))
  simp only [axisWallChart, ContinuousLinearEquiv.apply_symm_apply] at H
  have H' : normalizedWalls (axisWallChart (axisPermutation σ) h y) (σ j) =
      normalizedWalls (mainWallChart h y) j := by convert! H.symm using 1
  rw [H']
  fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisPermutationChart_other_wall_lt (σ : Equiv.Perm (Fin 3)) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ dominantWallChartDomain h) {j : Fin 3} (hj : j ≠ σ 0) :
    normalizedWalls (axisWallChart (axisPermutation σ) h y) j < h := by
  obtain ⟨l, rfl⟩ := σ.surjective j
  rw [axisPermutationChart_walls]
  fin_cases l
  · exact (hj rfl).elim
  · exact hy.2.1
  · exact hy.2.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisPermutationFamilyChart_injOn {ι : Type*} (σ : ι → Equiv.Perm (Fin 3)) {h : ℝ}
    {E : ι → Set SectionCoordinates} (hσ : Function.Injective (fun i => σ i 0))
    (hE : ∀ i, E i ⊆ dominantWallChartDomain h) :
    InjOn (axisFamilyChart (fun i => axisPermutation (σ i)) (fun _ => h)) (axisFamilySection E) := by
  rintro ⟨i, x⟩ hx ⟨j, y⟩ hy heq
  have hij : i = j := by
    apply hσ
    by_contra hne
    have H := axisPermutationChart_other_wall_lt (σ j) (hE j hy) hne
    change axisWallChart (axisPermutation (σ i)) h x = axisWallChart (axisPermutation (σ j)) h y at heq
    rw [← heq, axisPermutationChart_walls] at H
    exact (lt_irrefl h) H
  subst j
  have hxy : x = y := axisWallChart_injective (axisPermutation (σ i)) h heq
  exact Prod.ext rfl hxy

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.primaryAxisChart_injOn {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hE : ∀ i, E i ⊆ dominantWallChartDomain h) :
    InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) := by
  apply axisPermutationFamilyChart_injOn (fun i => Equiv.swap 0 i) _ hE
  intro i j hij
  simpa only [Equiv.swap_apply_left] using hij

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mem_dominantWallChartDomain_of_small {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h)
    (hb : Real.exp (-y 1) ≤ h / 8) (hc : Real.exp (-y 2) ≤ h / 8) :
    y ∈ dominantWallChartDomain h := by
  exact ⟨hy, lt_of_le_of_lt hb (by linarith), lt_of_le_of_lt hc (by linarith)⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuous_axisFamilyChart {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    (A : ι → NormalizedSymmetry) (h : ι → ℝ) : Continuous (axisFamilyChart A h) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  apply (A i).map.symm.continuous.comp
  change Continuous (mainWallChart (h i))
  unfold mainWallChart mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_measurable_primaryAxis_coordinates {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    (hE : ∀ i, MeasurableSet (E i))
    (hinj : InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E)) :
    ∃ c : NormalizedState → Fin 3 × SectionCoordinates, Measurable c ∧
      ∀ z ∈ axisFamilySection E, c (axisFamilyChart primaryAxisFrame (fun _ => h) z) = z := by
  classical
  by_cases hne : (axisFamilySection E).Nonempty
  · let : Nonempty (axisFamilySection E) := hne.to_subtype
    have H := (continuous_axisFamilyChart primaryAxisFrame (fun _ => h)).continuousOn.measurableEmbedding
      (measurableSet_axisFamilySection hE) hinj
    refine ⟨fun x => (H.invFun x).val, measurable_subtype_coe.comp H.measurable_invFun, ?_⟩
    intro z hz
    exact congrArg Subtype.val (H.leftInverse_invFun ⟨z, hz⟩)
  · exact ⟨fun _ => (0, 0), measurable_const, fun z hz => (hne ⟨z, hz⟩).elim⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.axisFamilyMeasure_constant_section {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (h : ℝ) {F : Set SectionCoordinates} (hF : MeasurableSet F) :
    axisFamilyMeasure (fun _ : ι => h) (axisFamilySection (fun _ => F)) =
      (Fintype.card ι : ℝ≥0∞) * mainWallMeasure h F := by
  rw [axisFamilyMeasure_apply _ (measurableSet_axisFamilySection (fun _ => hF))]
  simp [axisFamilySection, tsum_fintype]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.measurable_coreRestartFrame :
    Measurable (fun p : Fin 6 × CoreRestartData => coreRestartFrame p.1 p.2) := by
  have H : Measurable (fun p : Fin 6 × Fin 6 => (axisFrame_comp p.1 p.2).choose) :=
    measurable_of_countable _
  exact ((H.comp (measurable_snd.fst.fst.prodMk measurable_fst)).prodMk measurable_snd.fst.snd).prodMk
    measurable_snd.snd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.CoreRestartWitness.of_axisFrame {η σ Bcap : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (i : Fin 6)
    (H : CoreRestartWitness η J σ Bcap ((axisFrame i).map x) w) :
    CoreRestartWitness η J σ Bcap x (coreRestartFrame i w) := by
  obtain ⟨ht, hdom, p, hp, hstat, ho⟩ := H
  have hdom' : w.1.2 ∈ normalizedMaxDomain x 0 := by rwa [(axisFrame i).maxDomain] at hdom
  refine ⟨ht, hdom', p, hp, hstat, ?_⟩
  rwa [(axisFrame i).maxCurve hdom', (axisFrame_comp w.1.1 i).choose_spec] at ho

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.measurable_coreRestartDelay :
    Measurable (fun p : ℝ × CoreRestartData => coreRestartDelay p.1 p.2) := by
  exact (measurable_snd.fst.fst.prodMk (measurable_snd.fst.snd.add measurable_fst)).prodMk
    measurable_snd.snd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.CoreRestartWitness.of_forward {η σ Bcap s : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (H : CoreRestartWitness η J σ Bcap (normalizedMaxCurve x 0 s) w) :
    CoreRestartWitness η J σ Bcap x (coreRestartDelay s w) := by
  obtain ⟨ht, _, p, hp, hstat, ho⟩ := H
  have hTs : 0 < w.1.2 + s := add_pos_of_pos_of_nonneg ht hs
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hTs.le
  have hshift := normalizedMaxCurve_shift (t := w.1.2)
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs) hdom
  simp only [zero_add] at hshift
  exact ⟨hTs, hdom, p, hp, hstat, by simpa only [coreRestartDelay, hshift] using ho⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallSmallSection (d : ℝ) : MeasurableSet (mainWallSmallSection d) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_le hs measurable_const).inter (measurableSet_le hm measurable_const)

end
end

/-- A single global Borel map selects an exact statistical core outside one invariant exception null on every transverse section and in four-dimensional constraint coordinates. -/
theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∀ Bbound : ℝ, 0 < Bbound →
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
              ∀ x ∈ physicalPhaseSpace, x ∉ N →
                (W x).2.1 ≤ Bbound ∧ CoreRestartWitness η J σ Bcap x (W x) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartClosedSection_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, _, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro Bbound hBbound
  let h := min hS (1 / 16) / 2
  have hh : 0 < h := div_pos (lt_min hhS (by norm_num)) (by norm_num)
  have hhle : h ≤ min hS (1 / 16) := (half_lt_self (lt_min hhS (by norm_num))).le
  have hhmax : h ≤ 1 / 16 := hhle.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hhmax.trans (by norm_num)
  obtain ⟨_, _, HB⟩ := HS h ⟨hh, hhle.trans (min_le_left _ _)⟩
    50 90 550 (by norm_num) (by norm_num) (by norm_num) (1 / 128) (by norm_num)
  obtain ⟨dS, hdS, _, HdS⟩ := HB Bbound hBbound
  let d := min dS (h / 8) / 2
  have hd : 0 < d := div_pos (lt_min hdS (div_pos hh (by norm_num))) (by norm_num)
  have hdlt : d < min dS (h / 8) := half_lt_self (lt_min hdS (div_pos hh (by norm_num)))
  have hdh : d < h / 8 := hdlt.trans_le (min_le_right _ _)
  have hd1 : d ≤ 1 / 8 := hdh.le.trans (by linarith only [hh1])
  let F₀ := mainWallClosedFailure d
    (radialFailureSet d (1 / 128) (restartRadialFailureFamily h 50 d (1 / 128) 550 η J σ Bcap))
  obtain ⟨hF₀, _, _, hcompare, _, hfiniteOriginal, W₀, hW₀, Hgood⟩ :=
    HdS d ⟨hd, hdlt.le.trans (min_le_left _ _)⟩
  have hF₀finite : mainWallMeasure h F₀ ≠ ⊤ := ne_top_of_le_ne_top hfiniteOriginal hcompare
  let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
  let F := axisFamilySection (fun _ : Fin 3 => F₀)
  have hE : ∀ i, MeasurableSet (E i) := fun _ =>
    (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet
  have hF : MeasurableSet F := measurableSet_axisFamilySection (fun _ => hF₀)
  have hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤ := by
    rw [axisFamilyMeasure_constant_section h hF₀]
    exact ENNReal.mul_ne_top (by norm_num) hF₀finite
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
        Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1, (le_max_left _ _).trans (hy.1.2.trans hdh.le),
      (le_max_right _ _).trans (hy.1.2.trans hdh.le)⟩
  have hinj : InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) :=
    primaryAxisChart_injOn (fun i y hy => mem_dominantWallChartDomain_of_small hh
      (hsmall i y hy).1 (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2)
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, hhit⟩ :=
    exists_common_borel_success_exception hBirkhoff hBrehm hh hhmax hd hdh hF hfinite
  obtain ⟨τ, Y, hτ, hY, hflow, hfirst, _⟩ :=
    exists_smallAxis_borel_first_success hh hh1 hE hsmall hF hfinite
  obtain ⟨c, hcm, hcinv⟩ := exists_measurable_primaryAxis_coordinates hE hinj
  let Z := c ∘ Y
  have hZ : Measurable Z := hcm.comp hY
  let I : Fin 3 → Fin 6 := fun i => (axisOrder_covers (Equiv.swap 0 i)).choose
  have hI : Measurable I := measurable_of_countable _
  let V := fun x => coreRestartFrame (I (Z x).1) (W₀ (Z x).2)
  have hV : Measurable V := measurable_coreRestartFrame.comp ((hI.comp hZ.fst).prodMk (hW₀.comp hZ.snd))
  let W := fun x => coreRestartDelay (τ x) (V x)
  have hW : Measurable W := measurable_coreRestartDelay.comp (hτ.prodMk hV)
  refine ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, W, hW, ?_⟩
  intro x hx hn
  obtain ⟨ht, z, hz, heq⟩ := hfirst x hx.1 hx.2 (hhit x hx hn)
  have hZeq : Z x = z := by
    change c (Y x) = z
    rw [← heq]
    exact hcinv z hz.1
  have Hcanonical := (Hgood z.2 ⟨hz.1.1, hz.2⟩).2.2.1
  have Hframe : CoreRestartWitness η J σ Bcap
      ((axisFrame (I z.1)).map (axisFamilyChart primaryAxisFrame (fun _ => h) z)) (W₀ z.2) := by
    change CoreRestartWitness η J σ Bcap
      ((primaryAxisFrame z.1).map ((primaryAxisFrame z.1).map.symm (mainWallChart h z.2))) (W₀ z.2)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using Hcanonical
  have Hsuccess : CoreRestartWitness η J σ Bcap (Y x) (V x) := by
    dsimp only [V]
    rw [hZeq, ← heq]
    exact Hframe.of_axisFrame (I z.1)
  rw [hflow x] at Hsuccess
  refine ⟨?_, Hsuccess.of_forward hx.2 ht.1.1⟩
  change (W₀ (Z x).2).2.1 ≤ Bbound
  rw [hZeq]
  exact (Hgood z.2 ⟨hz.1.1, hz.2⟩).2.1

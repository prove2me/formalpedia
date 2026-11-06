-- Prove2me | solution 1 for BianchiIX.exists_primaryAxis_saturated_null_exception
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:38:49.601484+00:00
-- url     : https://prove2.me/submissions/c7c6016e-fcde-455c-8246-70aa99a365b8

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_rebase
import Theorems.Thm_BianchiIX_volume_transverseAxisWallOrbitPreimage
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.NullInFourCoordinates.iUnion {ι : Type*} [Countable ι]
    {S : ι → Set NormalizedState} (H : ∀ i, NullInFourCoordinates (S i)) :
    NullInFourCoordinates (⋃ i, S i) := by
  intro P hP
  rw [image_iUnion]
  exact measure_iUnion_null fun i => H i P hP

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.volume_tail_preimage_null {Z : Set (Fin 3 → ℝ)} (hZ : volume Z = 0) :
    volume {p : FourCoordinates | Fin.tail p ∈ Z} = 0 := by
  have hn : volume ((univ : Set ℝ) ×ˢ Z) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hZ, mul_zero]
  have H := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).quasiMeasurePreserving.preimage_null hn
  have heq : {p : FourCoordinates | Fin.tail p ∈ Z} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0) ⁻¹' ((univ : Set ℝ) ×ˢ Z) := by
    ext p
    simp [MeasurableEquiv.piFinSuccAbove]
  rw [heq]
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedMaxCurve_injOn (t₀ t : ℝ) :
    InjOn (fun x => normalizedMaxCurve x t₀ t) {x | t ∈ normalizedMaxDomain x t₀} := by
  intro x hx y hy heq
  dsimp only at heq
  have hx' := normalizedMaxCurve_rebase hx (initial_mem_normalizedMaxDomain x t₀)
  have hy' := normalizedMaxCurve_rebase hy (initial_mem_normalizedMaxDomain y t₀)
  rw [normalizedMaxCurve_initial] at hx' hy'
  rw [← hx', ← hy', heq]

end
end

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

private theorem BianchiIX.contDiffAt_mainWallChart {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (mainWallChart h) y := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiff_mainWallRadicand h n).contDiffAt.sqrt (ne_of_gt hy)).neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) y
  · exact contDiffAt_const
  · exact (contDiffAt_apply ℝ ℝ (1 : Fin 3) y).neg.exp
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 3) y).neg.exp

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_constraint {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (mainWallChart h y) = 1 := by
  have H := Real.sq_sqrt hy.le
  dsimp [stateConstraint, constraint, shearSq, mainWallChart]
  rw [neg_sq, H]
  unfold mainWallRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_negative {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : mainWallChart h y 0 < 0 :=
  neg_neg_of_pos (Real.sqrt_pos.mpr hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_positive {h : ℝ} (hh : 0 < h) (y : SectionCoordinates) :
    positiveWalls (mainWallChart h y) := ⟨hh, Real.exp_pos _, Real.exp_pos _⟩

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
open Set

private theorem BianchiIX.normalizedMaxCurve_inverse {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    -t ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) 0 ∧
      normalizedMaxCurve (normalizedMaxCurve x 0 t) 0 (-t) = x := by
  have hzero : 0 ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) t := by
    rw [normalizedMaxDomain_rebase ht]
    exact initial_mem_normalizedMaxDomain x 0
  refine ⟨(mem_normalizedMaxDomain_retime (t₀ := t)).mpr (by simpa using hzero), ?_⟩
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using ht)
    (show -t + t ∈ normalizedMaxDomain x 0 by simpa using initial_mem_normalizedMaxDomain x 0)
  simpa only [zero_add, neg_add_cancel, normalizedMaxCurve_initial] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.subset_normalizedOrbitSaturation (S : Set NormalizedState) : S ⊆ normalizedOrbitSaturation S :=
  fun x hx => ⟨x, hx, 0, initial_mem_normalizedMaxDomain x 0, normalizedMaxCurve_initial x 0⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mem_normalizedOrbitSaturation_flow {S : Set NormalizedState} {x : NormalizedState} {s : ℝ}
    (hx : x ∈ normalizedOrbitSaturation S) (hs : s ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 s ∈ normalizedOrbitSaturation S := by
  obtain ⟨z, hz, t, ht, rfl⟩ := hx
  have H := normalizedMaxCurve_restart (t := t + s) ht (by simpa using hs)
  exact ⟨z, hz, t + s, H.1, by simpa using H.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mem_normalizedOrbitSaturation_flow_iff {S : Set NormalizedState}
    {x : NormalizedState} {s : ℝ} (hs : s ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 s ∈ normalizedOrbitSaturation S ↔ x ∈ normalizedOrbitSaturation S := by
  constructor
  · intro hx
    have H := mem_normalizedOrbitSaturation_flow hx (normalizedMaxCurve_inverse hs).1
    rwa [(normalizedMaxCurve_inverse hs).2] at H
  · exact fun hx => mem_normalizedOrbitSaturation_flow hx hs

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.nullInFourCoordinates_orbitSaturation
    {C : (Fin 3 → ℝ) → NormalizedState} {Z : Set (Fin 3 → ℝ)}
    (hC : ∀ y ∈ Z, ContDiffAt ℝ 1 C y) (hZ : volume Z = 0) :
    NullInFourCoordinates (normalizedOrbitSaturation (C '' Z)) := by
  intro P hP
  let S : Set FourCoordinates := {p | Fin.tail p ∈ Z ∧
    p 0 ∈ normalizedMaxDomain (C (Fin.tail p)) 0}
  let F : FourCoordinates → NormalizedState := fun p => normalizedMaxCurve (C (Fin.tail p)) 0 (p 0)
  have hS : volume S = 0 := measure_mono_null (fun _ hp => hp.1) (volume_tail_preimage_null hZ)
  have hF (p : FourCoordinates) (hp : p ∈ S) : DifferentiableAt ℝ F p := by
    have htail : ContDiffAt ℝ 1 (fun q : FourCoordinates => Fin.tail q) p := by
      apply contDiffAt_pi.mpr
      intro i
      change ContDiffAt ℝ 1 (fun q : FourCoordinates => q i.succ) p
      fun_prop
    have htime : ContDiffAt ℝ 1 (fun q : FourCoordinates => q 0) p := by fun_prop
    have hpair := ((hC (Fin.tail p) hp.1).comp p htail).prodMk htime
    exact ((normalizedMaxCurve_regular hp.2).2.comp p hpair).differentiableAt (by norm_num)
  have hn : volume ((fun p => P (F p)) '' S) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun p hp => ((hP (F p)).comp p (hF p hp)).differentiableWithinAt) hS
  apply measure_mono_null _ hn
  rintro _ ⟨x, ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩, rfl⟩
  exact ⟨Fin.cons t z, by simpa [S] using And.intro hz ht, by simp [F]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mainWallChartDensity_pos {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) : 0 < mainWallChartDensity h y := by
  have hp := mainWallChart_negative hy
  have hS : 0 ≤ shearSq (mainWallChart h y 0) (y 0) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hH : 0 ≤ wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity
  exact div_pos (div_pos (by linarith) (mul_pos (by norm_num) (abs_pos.mpr (ne_of_lt hp))))
    (by linarith)

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
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_constraint (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (axisWallChart A h y) = 1 :=
  (A.symm.constraint (mainWallChart h y)).trans (mainWallChart_constraint hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_positive (A : NormalizedSymmetry) {h : ℝ} (hh : 0 < h) (y : SectionCoordinates) :
    positiveWalls (axisWallChart A h y) :=
  (A.symm.positive (mainWallChart h y)).mpr (mainWallChart_positive hh y)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_axisWallChart (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (axisWallChart A h) y :=
  A.map.symm.contDiff.contDiffAt.comp y (contDiffAt_mainWallChart hy n)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedEventRate_axisWall (A : NormalizedSymmetry) (x : NormalizedState) (t₀ t : ℝ) :
    normalizedEventRate (fun z => A.map z 2) x t₀ t =
      rateOne (A.map (normalizedMaxCurve x t₀ t) 0) (A.map (normalizedMaxCurve x t₀ t) 1) *
        A.map (normalizedMaxCurve x t₀ t) 2 := by
  unfold normalizedEventRate
  have hd : HasFDerivAt (fun z => A.map z 2)
      ((ContinuousLinearMap.proj (2 : Fin 5)).comp A.map.toContinuousLinearMap)
      (normalizedMaxCurve x t₀ t) := by
    convert! (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 5) (A.map (normalizedMaxCurve x t₀ t))).comp
      (normalizedMaxCurve x t₀ t) A.map.hasFDerivAt using 1
  rw [hd.fderiv]
  change A.map (normalizedField (normalizedMaxCurve x t₀ t)) 2 = _
  rw [← A.field]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_normalized_axisWall_event (A : NormalizedSymmetry) {x : NormalizedState} {t₀ t h : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hh : 0 < h)
    (hlevel : A.map (normalizedMaxCurve x t₀ t) 2 = h)
    (hp : A.map (normalizedMaxCurve x t₀ t) 0 < 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧ A.map (normalizedMaxCurve y t₀ (τ y)) 2 = h) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (A.map (normalizedMaxCurve z.1 t₀ z.2) 2 = h ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x := by
  have hrate : rateOne (A.map (normalizedMaxCurve x t₀ t) 0)
      (A.map (normalizedMaxCurve x t₀ t) 1) < 0 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg (A.map (normalizedMaxCurve x t₀ t) 0),
      sq_nonneg (A.map (normalizedMaxCurve x t₀ t) 1)]
  have htrans : normalizedEventRate (fun z => A.map z 2) x t₀ t ≠ 0 := by
    rw [normalizedEventRate_axisWall, hlevel]
    exact ne_of_lt (mul_neg_of_neg_of_pos hrate hh)
  have hg : ContDiffAt ℝ 1 (fun z => A.map z 2) (normalizedMaxCurve x t₀ t) := by fun_prop
  obtain ⟨τ, hτ, hcτ, _, hhit, huniq, hcMap, _⟩ := exists_normalized_event ht hg htrans
  refine ⟨τ, hτ, hcτ, ?_, ?_, hcMap⟩
  · filter_upwards [hhit] with y hy
    exact ⟨hy.1, hy.2.trans hlevel⟩
  · filter_upwards [huniq] with z hz
    simpa only [hlevel] using hz

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_mainWallChartDensity (h : ℝ) : Measurable (mainWallChartDensity h) := by
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    mainWallChart mainWallRadicand curvature wallAmplitude
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_absolutelyContinuous (h : ℝ) :
    mainWallMeasure h ≪ volume.restrict (mainWallChartDomain h) := withDensity_absolutelyContinuous _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_restrict_absolutelyContinuous_mainWallMeasure {h : ℝ} (hh : 0 < h) :
    volume.restrict (mainWallChartDomain h) ≪ mainWallMeasure h := by
  apply withDensity_absolutelyContinuous' (measurable_mainWallChartDensity h).ennreal_ofReal.aemeasurable
  apply ae_restrict_of_forall_mem (isOpen_mainWallChartDomain h).measurableSet
  intro y hy
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (mainWallChartDensity_pos hh hy))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_null_iff {h : ℝ} (hh : 0 < h) (A : Set SectionCoordinates) :
    mainWallMeasure h A = 0 ↔ (volume.restrict (mainWallChartDomain h)) A = 0 :=
  ⟨fun hA => volume_restrict_absolutelyContinuous_mainWallMeasure hh hA,
    fun hA => mainWallMeasure_absolutelyContinuous h hA⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_axisWallFlowDomain (A : NormalizedSymmetry) (h : ℝ) : IsOpen (axisWallFlowDomain A h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hpair : ContinuousAt (fun q : SectionCoordinates × ℝ => (axisWallChart A h q.1, q.2)) p :=
    ((contDiffAt_axisWallChart A hp.1 1).continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  exact (continuousAt_fst.eventually ((isOpen_mainWallChartDomain h).mem_nhds hp.1)).and
    (hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_axisWallFlowMap (A : NormalizedSymmetry) {h : ℝ} {p : SectionCoordinates × ℝ}
    (hp : p ∈ axisWallFlowDomain A h) : ContDiffAt ℝ 1 (axisWallFlowMap A h) p := by
  have H := normalizedMaxCurve_regular (x := axisWallChart A h p.1) (t₀ := 0) (t := p.2) hp.2
  exact H.2.comp p
    (((contDiffAt_axisWallChart A hp.1 1).comp p contDiffAt_fst).prodMk contDiffAt_snd)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_axisWallFlowMap_injOn (A : NormalizedSymmetry) {h : ℝ} (hh : 0 < h)
    {p : SectionCoordinates × ℝ} (hp : p ∈ axisWallFlowDomain A h) :
    ∃ V : Set (SectionCoordinates × ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ axisWallFlowDomain A h ∧
      InjOn (axisWallFlowMap A h) V := by
  have hinv := normalizedMaxCurve_inverse hp.2
  have hlevel : A.map (normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2)) 2 = h := by
    rw [show normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2) = axisWallChart A h p.1 from hinv.2,
      axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hneg : A.map (normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2)) 0 < 0 := by
    rw [show normalizedMaxCurve (axisWallFlowMap A h p) 0 (-p.2) = axisWallChart A h p.1 from hinv.2,
      axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative hp.1
  obtain ⟨τ, _, _, _, huniq, _⟩ := exists_normalized_axisWall_event A hinv.1 hh hlevel hneg
  have hpair : ContinuousAt (fun q : SectionCoordinates × ℝ => (axisWallFlowMap A h q, -q.2)) p :=
    (contDiffAt_axisWallFlowMap A hp).continuousAt.prodMk continuousAt_snd.neg
  have hrecover : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p,
      q ∈ axisWallFlowDomain A h ∧ τ (axisWallFlowMap A h q) = -q.2 := by
    filter_upwards [(isOpen_axisWallFlowDomain A h).mem_nhds hp, hpair.eventually huniq] with q hq he
    refine ⟨hq, he.2.mp ?_⟩
    rw [show normalizedMaxCurve (axisWallFlowMap A h q) 0 (-q.2) = axisWallChart A h q.1 from
      (normalizedMaxCurve_inverse hq.2).2, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hrecover
  refine ⟨V, hVo, hpV, fun _ hq => (hV hq).1, ?_⟩
  intro q hq r hr heq
  have htime : q.2 = r.2 := by
    have H := congrArg τ heq
    rw [(hV hq).2, (hV hr).2] at H
    exact neg_injective H
  apply Prod.ext _ htime
  apply axisWallChart_injective A h
  apply normalizedMaxCurve_injOn 0 q.2 (hV hq).1.2
    (by rw [htime]; exact (hV hr).1.2)
  simpa only [axisWallFlowMap, htime] using heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.axisWallOrbitSaturation_eq_image (A : NormalizedSymmetry) {h : ℝ}
    {Z : Set SectionCoordinates} (hZ : Z ⊆ mainWallChartDomain h) :
    normalizedOrbitSaturation (axisWallChart A h '' Z) =
      axisWallFlowMap A h '' ((Prod.fst ⁻¹' Z) ∩ axisWallFlowDomain A h) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩
    exact ⟨(z, t), ⟨hz, hZ hz, ht⟩, rfl⟩
  · rintro ⟨p, ⟨hz, hp⟩, rfl⟩
    exact ⟨axisWallChart A h p.1, mem_image_of_mem _ hz, p.2, hp.2, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.measurableSet_axisWallFlowMap_image (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {S : Set (SectionCoordinates × ℝ)} (hS : MeasurableSet S)
    (hdom : S ⊆ axisWallFlowDomain A h) : MeasurableSet (axisWallFlowMap A h '' S) := by
  classical
  by_cases hne : S.Nonempty
  · let : Nonempty S := hne.to_subtype
    choose V hVo hpV hVD hVinj using
      (fun p : S => exists_axisWallFlowMap_injOn A hh (hdom p.property))
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
    have heq : axisWallFlowMap A h '' S = ⋃ n : ℕ, axisWallFlowMap A h '' (S ∩ V (f n)) := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hp)
        exact mem_iUnion.mpr ⟨n, p, ⟨hp, hn⟩, rfl⟩
      · rintro hx
        obtain ⟨n, p, hp, rfl⟩ := mem_iUnion.mp hx
        exact mem_image_of_mem _ hp.1
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact (hS.inter (hVo (f n)).measurableSet).image_of_continuousOn_injOn
      (fun p hp => (contDiffAt_axisWallFlowMap A (hdom hp.1)).continuousAt.continuousWithinAt)
      ((hVinj (f n)).mono inter_subset_right)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, image_empty]
    exact MeasurableSet.empty

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.measurableSet_axisWallOrbitSaturation (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h)
    (hZ : MeasurableSet Z) : MeasurableSet (normalizedOrbitSaturation (axisWallChart A h '' Z)) := by
  rw [axisWallOrbitSaturation_eq_image A hchart]
  exact measurableSet_axisWallFlowMap_image A hh
    ((hZ.preimage measurable_fst).inter (isOpen_axisWallFlowDomain A h).measurableSet)
    inter_subset_right

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.axisWallOrbitSaturation_physical (A : NormalizedSymmetry) {h : ℝ}
    (hh : 0 < h) {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h)
    {x : NormalizedState} (hx : x ∈ normalizedOrbitSaturation (axisWallChart A h '' Z)) :
    positiveWalls x ∧ stateConstraint x = 1 := by
  obtain ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩ := hx
  exact (maximalNormalizedSolution (axisWallChart A h z) 0).physical
    (axisWallChart_positive A hh z) (axisWallChart_constraint A (hchart hz)) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.preimage_axisWallOrbitSaturation (A : NormalizedSymmetry) (C : SectionCoordinates → NormalizedState)
    (h : ℝ) (Z : Set SectionCoordinates) :
    C ⁻¹' normalizedOrbitSaturation (axisWallChart A h '' Z) = transverseAxisWallOrbitPreimage C A h 0 Z := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, t, ht, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [heq] at H
    exact ⟨-t, H.1, z, hz, H.2.symm⟩
  · rintro ⟨t, ht, z, hz, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [← heq] at H
    exact ⟨axisWallChart A h z, mem_image_of_mem _ hz, -t, H.1, H.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.volume_preimage_axisWallOrbitSaturation (A : NormalizedSymmetry) {h : ℝ}
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hh : 0 < h) (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h) (hZ : volume Z = 0) :
    volume (U ∩ C ⁻¹' normalizedOrbitSaturation (axisWallChart A h '' Z)) = 0 := by
  rw [preimage_axisWallOrbitSaturation]
  exact volume_transverseAxisWallOrbitPreimage A hh hU hC hp hc hflux hchart hZ

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.ae_axisFamilyMeasure_iff {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (k : ι → ℝ) (P : ι × SectionCoordinates → Prop) :
    (∀ᵐ z ∂axisFamilyMeasure k, P z) ↔ ∀ i, ∀ᵐ y ∂mainWallMeasure (k i), P (i, y) := by
  rw [axisFamilyMeasure, Measure.ae_sum_iff]
  exact forall_congr' (fun i => (measurableEmbedding_prodMk_left i).ae_map_iff)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.volume_axisFamily_exceptional_slice {h : ℝ} (hh : 0 < h)
    {E : Fin 3 → Set SectionCoordinates} {P : Fin 3 × SectionCoordinates → Prop}
    (hE : ∀ i, E i ⊆ mainWallChartDomain h)
    (H : ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E → P z)
    (i : Fin 3) : volume {y | y ∈ E i ∧ ¬P (i, y)} = 0 := by
  have Hi := (ae_axisFamilyMeasure_iff _ _).mp H i
  have hae : ∀ᵐ y ∂mainWallMeasure h, ¬(y ∈ E i ∧ ¬P (i, y)) := by
    filter_upwards [Hi] with y hy hbad
    exact hbad.2 (hy hbad.1)
  have hnull : mainWallMeasure h {y | y ∈ E i ∧ ¬P (i, y)} = 0 := by
    simpa only [ae_iff, not_not] using hae
  have Hvol := (mainWallMeasure_null_iff hh _).mp hnull
  rwa [Measure.restrict_apply' (isOpen_mainWallChartDomain h).measurableSet,
    inter_eq_left.mpr (fun _ hy => hE i hy.1)] at Hvol

end
end


/-- One Borel invariant exception, independent of the source chart, contains all exceptional section points. -/
theorem solution {h : ℝ} (hh : 0 < h)
    {E : Fin 3 → Set SectionCoordinates} {P : Fin 3 × SectionCoordinates → Prop}
    (hE : ∀ i, MeasurableSet (E i)) (hchart : ∀ i, E i ⊆ mainWallChartDomain h)
    (H : ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E → P z) :
    ∃ N : Set NormalizedState, MeasurableSet N ∧
      (∀ x ∈ N, positiveWalls x ∧ stateConstraint x = 1) ∧
      (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0, normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
      (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
        IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
        (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
        (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
        volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
      ∀ z ∈ axisFamilySection E, axisFamilyChart primaryAxisFrame (fun _ => h) z ∉ N → P z := by
  classical
  let Z : Fin 3 → Set SectionCoordinates := fun i =>
    toMeasurable volume {y | y ∈ E i ∧ ¬P (i, y)} ∩ E i
  have hZ (i : Fin 3) : MeasurableSet (Z i) := (measurableSet_toMeasurable _ _).inter (hE i)
  have hZchart (i : Fin 3) : Z i ⊆ mainWallChartDomain h := fun _ hz => hchart i hz.2
  have hZnull (i : Fin 3) : volume (Z i) = 0 := by
    apply measure_mono_null inter_subset_left
    rw [measure_toMeasurable]
    exact volume_axisFamily_exceptional_slice hh hchart H i
  let N := ⋃ i : Fin 3, normalizedOrbitSaturation (axisWallChart (primaryAxisFrame i) h '' Z i)
  refine ⟨N, MeasurableSet.iUnion (fun i =>
    measurableSet_axisWallOrbitSaturation (primaryAxisFrame i) hh (hZchart i) (hZ i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact axisWallOrbitSaturation_physical (primaryAxisFrame i) hh (hZchart i) hi
  · intro x t ht
    simp only [N, mem_iUnion, mem_normalizedOrbitSaturation_flow_iff ht]
  · intro C U hU hC hp hc hflux
    have heq : U ∩ C ⁻¹' N = ⋃ i : Fin 3,
        U ∩ C ⁻¹' normalizedOrbitSaturation (axisWallChart (primaryAxisFrame i) h '' Z i) := by
      ext y
      simp only [N, mem_inter_iff, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨hy, i, hi⟩; exact ⟨i, hy, hi⟩
      · rintro ⟨i, hy, hi⟩; exact ⟨hy, i, hi⟩
    rw [heq]
    exact measure_iUnion_null fun i => volume_preimage_axisWallOrbitSaturation (primaryAxisFrame i)
      hh hU hC hp hc hflux (hZchart i) (hZnull i)
  · exact NullInFourCoordinates.iUnion fun i => nullInFourCoordinates_orbitSaturation
      (fun _ hy => contDiffAt_axisWallChart (primaryAxisFrame i) (hZchart i hy) 1) (hZnull i)
  · intro z hz hn
    by_contra hp
    have hzZ : z.2 ∈ Z z.1 := ⟨subset_toMeasurable volume _ ⟨hz, hp⟩, hz⟩
    apply hn
    exact mem_iUnion.mpr ⟨z.1, subset_normalizedOrbitSaturation _ (mem_image_of_mem _ hzZ)⟩

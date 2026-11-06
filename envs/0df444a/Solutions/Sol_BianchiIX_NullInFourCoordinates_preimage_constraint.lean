-- Prove2me | solution 1 for BianchiIX.NullInFourCoordinates.preimage_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:05:21.910421+00:00
-- url     : https://prove2.me/submissions/95c945ea-74b1-4075-943d-552f7003709c

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exists_local_null_preimage {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
      ∀ Z : Set (Fin n → ℝ), volume Z = 0 → volume (U ∩ f ⁻¹' Z) = 0 := by
  let L := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hd : HasFDerivAt f (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [show (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ f x from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let g := hf.localInverse hd (by norm_num)
  have hg : ContDiffAt ℝ 1 g (f x) := hf.to_localInverse hd (by norm_num)
  have hleft : ∀ᶠ y in 𝓝 x, g (f y) = y := (hf.hasStrictFDerivAt' hd (by norm_num)).eventually_left_inverse
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (hg.eventually (by norm_num))
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp
    ((hf.continuousAt.eventually (hVo.mem_nhds hxV)).and hleft)
  refine ⟨U, hUo, hxU, fun Z hZ => ?_⟩
  have hnull : volume (g '' (Z ∩ V)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => ((show ContDiffAt ℝ 1 g z from hV hz.2).differentiableAt
        (by norm_num)).differentiableWithinAt)
      (measure_mono_null inter_subset_left hZ)
  apply measure_mono_null _ hnull
  intro y hy
  exact ⟨f y, ⟨hy.2, (hU hy.1).1⟩, (hU hy.1).2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_eq_zero_of_local_null {n : ℕ} {S : Set (Fin n → ℝ)}
    (H : ∀ x ∈ S, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ volume (S ∩ U) = 0) :
    volume S = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose U hU hxU hnull using (fun x : S => H x.val x.property)
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover U hU
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
    apply measure_mono_null (t := ⋃ m : ℕ, S ∩ U (f m)) _
      (measure_iUnion_null fun m => hnull (f m))
    intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hx)
    exact mem_iUnion.mpr ⟨m, hx, hm⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, measure_empty]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.NullInFourCoordinates.preimage {S : Set NormalizedState} (H : NullInFourCoordinates S)
    {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hinj : ∀ y ∈ U, Function.Injective (fderiv ℝ C y)) :
    volume (U ∩ C ⁻¹' S) = 0 := by
  apply volume_eq_zero_of_local_null
  intro y hy
  obtain ⟨A, hA⟩ := (fderiv ℝ C y).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hinj y hy.1))
  let P : NormalizedState →L[ℝ] FourCoordinates := A.toContinuousLinearMap
  have hcomp : P.comp (fderiv ℝ C y) = ContinuousLinearMap.id ℝ FourCoordinates := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : FourCoordinates →ₗ[ℝ] FourCoordinates => L v) hA
  have hderiv : HasFDerivAt (fun z => P (C z)) (ContinuousLinearMap.id ℝ FourCoordinates) y := by
    have hd := P.hasFDerivAt.comp y ((hC y hy.1).differentiableAt (by norm_num)).hasFDerivAt
    rwa [hcomp] at hd
  have hsmooth := P.contDiff.contDiffAt.comp y (hC y hy.1)
  have hdet : (fderiv ℝ (fun z => P (C z)) y).det ≠ 0 := by
    rw [hderiv.fderiv]
    change LinearMap.det (LinearMap.id : FourCoordinates →ₗ[ℝ] FourCoordinates) ≠ 0
    rw [LinearMap.det_id]
    exact one_ne_zero
  obtain ⟨V, hVo, hyV, hV⟩ := exists_local_null_preimage hsmooth hdet
  refine ⟨V, hVo, hyV, measure_mono_null ?_ (hV (P '' S) (H P P.differentiable))⟩
  intro z hz
  exact ⟨hz.2, mem_image_of_mem P hz.1.2⟩

end
end

private theorem BianchiIX.injective_of_normalizedConstraintVolume_ne_zero {x : NormalizedState}
    {L : FourCoordinates →L[ℝ] NormalizedState}
    (hvol : normalizedConstraintVolume x (fun i => L (Pi.single i 1)) ≠ 0) :
    Function.Injective L := by
  have hdet : normalizedAmbientVolume (Fin.cons ((1 / 2 : ℝ) • x)
      (fun i => L (Pi.single i 1))) ≠ 0 := by
    intro hz
    apply hvol
    simp only [normalizedConstraintVolume, hz, zero_div]
  have hli := ((Pi.basisFun ℝ (Fin 5)).is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)).1
  have hfour : LinearIndependent ℝ (fun i : Fin 4 => L (Pi.single i 1)) := by
    simpa only [Function.comp_def, Fin.cons_succ] using hli.comp Fin.succ (Fin.succ_injective 4)
  have hsum (v : FourCoordinates) : ∑ i, v i • L (Pi.single i 1) = L v := by
    simp only [← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  intro v w hvw
  apply hfour.fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply, hsum] using hvw


/-- Nullity for the intrinsic constraint volume in any regular physical coordinates. -/
theorem solution {S : Set NormalizedState}
    (H : NullInFourCoordinates S) {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hv : ∀ y ∈ U, normalizedConstraintVolume (C y)
      (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) : volume (U ∩ C ⁻¹' S) = 0 :=
  H.preimage hC (fun y hy => injective_of_normalizedConstraintVolume_ne_zero (hv y hy))

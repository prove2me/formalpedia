-- Prove2me | solution 1 for BianchiIX.ae_primaryAxis_success_of_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:17:42.703469+00:00
-- url     : https://prove2.me/submissions/1e318140-9b91-4391-9262-64e115fda197

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraCodingData
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_typicalSurvivors_ae_eq
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_append
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_nil
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_level
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_typicalSurvivors
import Theorems.Thm_BianchiIX_InverseBranchTree_survivors_subset_root
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_nil
import Theorems.Thm_BianchiIX_InverseBranchTree_word_succ
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_NormalizedSymmetry_sectionFlux
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_eraAmplitude_le
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Theorems.Thm_BianchiIX_eraAmplitude_zero
import Theorems.Thm_BianchiIX_era_distortion_budget
import Theorems.Thm_BianchiIX_exists_arbitrarily_late_compact_core
import Theorems.Thm_BianchiIX_exists_arbitrarily_late_primaryAxis_crossing
import Theorems.Thm_BianchiIX_exists_axisFamily_firstReturn
import Theorems.Thm_BianchiIX_exists_axisWall_coordinate_event
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_compactEraHistories_of_taub_avoidance
import Theorems.Thm_BianchiIX_exists_era_budget_threshold
import Theorems.Thm_BianchiIX_exists_era_curve_step
import Theorems.Thm_BianchiIX_exists_era_input_estimates
import Theorems.Thm_BianchiIX_exists_era_output_estimates
import Theorems.Thm_BianchiIX_exists_era_selected_inputs_inverse
import Theorems.Thm_BianchiIX_exists_local_null_scalar_level
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasFDerivAt_normalizedMaxCurve
import Theorems.Thm_BianchiIX_mainWallChart_signed_flux
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
import Theorems.Thm_BianchiIX_normalizedSectionFlux_add_flow
import Theorems.Thm_BianchiIX_normalizedSectionFlux_flow
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_eq_exp_integral
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_not_bounded_digits_of_typical
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
open scoped Topology ENNReal

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
noncomputable section
open BianchiIX
open MeasureTheory
open scoped ENNReal

private theorem BianchiIX.lintegral_three_coordinates {f : (Fin 3 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z) = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ r : ℝ, f ![r, x, y] := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1
  have he : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1)
  rw [← he.lintegral_comp hf]
  change (∫⁻ p, (f ∘ e.symm) p ∂(volume.prod volume)) = _
  rw [lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro x
  let g := fun v : Fin 2 → ℝ => f (e.symm (x, v))
  have hg : Measurable g := hf.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  let e₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he₂ : MeasurePreserving e₂.symm volume volume :=
    MeasurePreserving.symm e₂ (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  change (∫⁻ v, g v) = _
  rw [← he₂.lintegral_comp hg]
  change (∫⁻ p, (g ∘ e₂.symm) p ∂(volume.prod volume)) = _
  rw [lintegral_prod_symm _ (hg.comp e₂.symm.measurable).aemeasurable]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro r
  change f (e.symm (x, e₂.symm (r, y))) = f ![r, x, y]
  apply congrArg f
  ext i
  fin_cases i <;> rfl

end
end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem BianchiIX.null_of_strict_expansion
    {A : Set X} {R : X → X} {j : X → ℝ≥0∞}
    (hfinite : μ A ≠ ∞)
    (hj : AEMeasurable j (μ.restrict A))
    (hexpand : ∀ᵐ x ∂μ.restrict A, 1 < j x)
    (hchange : μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hinvariant : R '' A ⊆ A) : μ A = 0 := by
  by_contra hpos
  have hμ : μ.restrict A ≠ 0 := by
    simpa using hpos
  have hlt := lintegral_strict_mono (f := fun _ : X => (1 : ℝ≥0∞))
    hμ hj (by simpa using hfinite) hexpand
  have : μ A < μ (R '' A) := by simpa [hchange] using hlt
  exact (not_lt_of_ge (measure_mono hinvariant)) this

end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem BianchiIX.permanentFailure_measurable
    {R : X → X} {D E : Set X}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E) :
    MeasurableSet (permanentFailure R D E) := by
  simp only [permanentFailure, ofPred_forall]
  exact MeasurableSet.iInter fun n => (hD.inter hE).preimage (hR.iterate n)

end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
private theorem BianchiIX.permanentFailure_subset {R : X → X} {D E : Set X} :
    permanentFailure R D E ⊆ D ∩ E := by
  intro x hx
  exact hx 0

end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
private theorem BianchiIX.permanentFailure_invariant {R : X → X} {D E : Set X} :
    R '' permanentFailure R D E ⊆ permanentFailure R D E := by
  rintro _ ⟨x, hx, rfl⟩ n
  simpa only [Function.iterate_succ_apply] using hx (n + 1)

end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem BianchiIX.permanentFailure_null
    {R : X → X} {D E : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hfinite : μ E ≠ ∞) (hj : Measurable j)
    (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ B, MeasurableSet B → B ⊆ D →
      μ (R '' B) = ∫⁻ x in B, j x ∂μ) :
    μ (permanentFailure R D E) = 0 := by
  have hA := permanentFailure_measurable hR hD hE
  have hAD : permanentFailure R D E ⊆ D :=
    fun _ hx => (permanentFailure_subset hx).1
  have hAE : permanentFailure R D E ⊆ E :=
    fun _ hx => (permanentFailure_subset hx).2
  apply null_of_strict_expansion
    (ne_top_of_le_ne_top hfinite (measure_mono hAE)) hj.aemeasurable
    _ (hchange _ hA hAD) permanentFailure_invariant
  exact (ae_restrict_mem hA).mono fun x hx => hexpand x (hAD hx)

end

section
open MeasureTheory Set
open scoped ENNReal
open BianchiIX
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem BianchiIX.ae_eventually_leaves_failure
    {R : X → X} {D E : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hfinite : μ E ≠ ∞) (hj : Measurable j)
    (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ B, MeasurableSet B → B ⊆ D →
      μ (R '' B) = ∫⁻ x in B, j x ∂μ) :
    ∀ᵐ x ∂μ, (∀ n : ℕ, R^[n] x ∈ D) → ∃ n : ℕ, R^[n] x ∉ E := by
  have hnull := permanentFailure_null hR hD hE hfinite hj hexpand hchange
  have houtside : ∀ᵐ x ∂μ, x ∉ permanentFailure R D E := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hnull
  filter_upwards [houtside] with x hx hreturns
  by_contra h
  push Not at h
  exact hx (fun n => ⟨hreturns n, h n⟩)

end

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.volume_fst_image_eq_zero_of_local_null {n : ℕ} {S : Set ((Fin n → ℝ) × ℝ)}
    (H : ∀ p ∈ S, ∃ V : Set ((Fin n → ℝ) × ℝ), IsOpen V ∧ p ∈ V ∧
      ∃ Z : Set (Fin n → ℝ), volume Z = 0 ∧ ∀ q ∈ S ∩ V, q.1 ∈ Z) :
    volume (Prod.fst '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose V hVo hpV Z hZ hcover using (fun p : S => H p.val p.property)
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
    apply measure_mono_null (t := ⋃ m : ℕ, Z (f m)) _ (measure_iUnion_null fun m => hZ (f m))
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hp)
    exact mem_iUnion.mpr ⟨m, hcover (f m) p ⟨hp, hm⟩⟩
  · simp only [Set.not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusSq_nonneg (s b c : ℝ) : 0 ≤ taubRadiusSq s b c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

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

private theorem BianchiIX.volume_regular_scalar_level {n : ℕ} {g : (Fin n → ℝ) → ℝ} {S : Set (Fin n → ℝ)}
    (hg : ∀ x ∈ S, ContDiffAt ℝ 1 g x) (hz : ∀ x ∈ S, g x = 0)
    (hd : ∀ x ∈ S, ∃ i : Fin n, fderiv ℝ g x (Pi.single i 1) ≠ 0) :
    volume S = 0 := by
  apply volume_eq_zero_of_local_null
  intro x hx
  obtain ⟨i, hi⟩ := hd x hx
  obtain ⟨U, hU, hxU, hnull⟩ := exists_local_null_scalar_level (hg x hx) hi
  refine ⟨U, hU, hxU, measure_mono_null ?_ hnull⟩
  exact fun y hy => ⟨hy.2, hz y hy.1⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.small_section_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    curvature h b c ≤ (25 / 16) * h ^ 2 ∧
      (983 / 1024 : ℝ) ≤ p ^ 2 ∧ p ≤ -15 / 16 ∧ shearSq p s ≤ 2 := by
  have hsum : h + b + c ≤ 5 / 4 * h := by linarith
  have hsum2 := pow_le_pow_left₀ (by linarith : 0 ≤ h + b + c) hsum 2
  have hcurv := abs_le.mp (curvature_abs_le_sum_sq hh.le hb hc)
  have hQ : curvature h b c ≤ (25 / 16) * h ^ 2 := by nlinarith
  have hQlo : -(25 / 16) * h ^ 2 ≤ curvature h b c := by nlinarith
  have hh2 : h ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hh.le hh1 2
  have hs2 : s ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hs)
  have hcon : p ^ 2 + s ^ 2 + curvature h b c = 1 := hconstraint
  have hp2 : (983 / 1024 : ℝ) ≤ p ^ 2 := by nlinarith
  refine ⟨hQ, hp2, ?_, ?_⟩
  · nlinarith [sq_nonneg (p + 15 / 16)]
  · unfold shearSq
    nlinarith

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.finite_compact_transverse_level {K : Set ℝ} {f df : ℝ → ℝ} {h : ℝ}
    (hK : IsCompact K) (hlevel : ∀ t ∈ K, f t = h)
    (hderiv : ∀ t ∈ K, HasDerivAt f (df t) t) (hne : ∀ t ∈ K, df t ≠ 0) : K.Finite := by
  apply hK.finite
  rw [isDiscrete_iff_nhdsNE]
  intro t ht
  rw [inf_principal_eq_bot]
  have H : ∀ᶠ u in 𝓝[≠] t, slope f t u ≠ 0 :=
    (hderiv t ht).tendsto_slope.eventually (eventually_ne_nhds (hne t ht))
  filter_upwards [H] with u hu
  intro huK
  exact hu (by simp [slope, hlevel u huK, hlevel t ht])

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.finite_negative_section_times {K : Set ℝ} {a p s : ℝ → ℝ} {h ε : ℝ}
    (hK : IsCompact K) (ha : ContinuousOn a K) (hp : ContinuousOn p K)
    (hh : 0 < h) (hε : 0 < ε)
    (hODE : ∀ t ∈ K, HasDerivAt a (rateOne (p t) (s t) * a t) t) :
    {t ∈ K | a t = h ∧ p t ≤ -ε}.Finite := by
  let S : Set ℝ := {t ∈ K | a t = h ∧ p t ≤ -ε}
  have hS : IsCompact S := by
    obtain ⟨U, hU, heq⟩ := continuousOn_iff_isClosed.mp (ha.prodMk hp)
      ({h} ×ˢ Iic (-ε)) (isClosed_singleton.prod isClosed_Iic)
    have H : IsCompact ((fun t => (a t, p t)) ⁻¹' ({h} ×ˢ Iic (-ε)) ∩ K) := by
      rw [heq]
      exact hK.inter_left hU
    convert! H using 1
    ext t
    simp only [S, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_Iic]
    tauto
  apply finite_compact_transverse_level (df := fun t => rateOne (p t) (s t) * a t) hS
    (fun t ht => ht.2.1) (fun t ht => hODE t ht.1)
  intro t ht
  have hpt : p t ≤ -ε := ht.2.2
  have hr : rateOne (p t) (s t) < 0 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg (p t), sq_nonneg (s t)]
  exact ne_of_lt (mul_neg_of_neg_of_pos hr (ht.2.1 ▸ hh))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

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
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_coordinates {h : ℝ} {x : NormalizedState}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) (hp : x 0 < 0) (hh : x 2 = h) :
    mainWallCoordinates x ∈ mainWallChartDomain h ∧ mainWallChart h (mainWallCoordinates x) = x := by
  have hr : mainWallRadicand h (mainWallCoordinates x) = x 0 ^ 2 := by
    change 1 - x 1 ^ 2 - curvature h (Real.exp (- -Real.log (x 3)))
      (Real.exp (- -Real.log (x 4))) = x 0 ^ 2
    rw [neg_neg, neg_neg, Real.exp_log hpos.2.1, Real.exp_log hpos.2.2]
    have H : x 0 ^ 2 + x 1 ^ 2 + curvature h (x 3) (x 4) = 1 := by
      simpa only [stateConstraint, constraint, shearSq, hh] using hcon
    linarith
  refine ⟨by change 0 < mainWallRadicand h (mainWallCoordinates x)
             rw [hr]; exact sq_pos_of_ne_zero (ne_of_lt hp), ?_⟩
  ext i
  fin_cases i
  · change -Real.sqrt (mainWallRadicand h (mainWallCoordinates x)) = x 0
    rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp, neg_neg]
  · rfl
  · exact hh.symm
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.1]
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.2]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_mainWallChart {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    HasFDerivAt (mainWallChart h) (mainWallChartDifferential h y) y :=
  ((contDiffAt_mainWallChart hy 1).differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_normalized_arrival {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (ht : τ x ∈ normalizedMaxDomain x t₀)
    (hτ : DifferentiableAt ℝ τ x) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ (τ y))
      (normalizedFlowDifferential x t₀ (τ x) +
        (fderiv ℝ τ x).smulRight (normalizedField (normalizedMaxCurve x t₀ (τ x)))) x := by
  convert! (hasFDerivAt_normalizedMaxCurve ht).comp x
    ((hasFDerivAt_id x).prodMk hτ.hasFDerivAt) using 1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedSectionFlux_arrival {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : τ x ∈ normalizedMaxDomain x t₀) (hτ : DifferentiableAt ℝ τ x)
    (v : Fin 3 → NormalizedState) (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedSectionFlux (normalizedMaxCurve x t₀ (τ x))
        (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i)) =
      normalizedVolumeJacobian x t₀ (τ x) * normalizedSectionFlux x v := by
  rw [(hasFDerivAt_normalized_arrival ht hτ).fderiv,
    ← normalizedSectionFlux_flow hpos hcon ht v hv]
  unfold normalizedSectionFlux normalizedConstraintVolume
  congr 1
  exact normalizedSectionFlux_add_flow (normalizedMaxCurve x t₀ (τ x))
    ((1 / 2 : ℝ) • normalizedMaxCurve x t₀ (τ x))
    (fun i => normalizedFlowDifferential x t₀ (τ x) (v i))
    (fun i => fderiv ℝ τ x (v i))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedSectionFlux_arrival_abs {x : NormalizedState} {t₀ : ℝ}
    {τ : NormalizedState → ℝ} (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : τ x ∈ normalizedMaxDomain x t₀) (hτ : DifferentiableAt ℝ τ x)
    (v : Fin 3 → NormalizedState) (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    |normalizedSectionFlux (normalizedMaxCurve x t₀ (τ x))
        (fun i => fderiv ℝ (fun y => normalizedMaxCurve y t₀ (τ y)) x (v i))| =
      Real.exp (∫ u in t₀..τ x, normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u)) *
        |normalizedSectionFlux x v| := by
  rw [normalizedSectionFlux_arrival hpos hcon ht hτ v hv,
    normalizedVolumeJacobian_eq_exp_integral hpos hcon ht, abs_mul, abs_of_pos (Real.exp_pos _)]

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

private theorem BianchiIX.normalizedSectionFlux_comp (x : NormalizedState)
    (L : SectionCoordinates →L[ℝ] NormalizedState) (D : SectionCoordinates →L[ℝ] SectionCoordinates) :
    normalizedSectionFlux x (fun i => L (D (Pi.single i 1))) =
      D.det * normalizedSectionFlux x (fun i => L (Pi.single i 1)) := by
  let f : SectionCoordinates [⋀^Fin 3]→ₗ[ℝ] ℝ :=
    (normalizedVolumeWeight x)⁻¹ •
      ((normalizedAmbientVolume.curryLeft ((1 / 2 : ℝ) • x)).curryLeft (normalizedField x)).compLinearMap L.toLinearMap
  let b := Pi.basisFun ℝ (Fin 3)
  have hd : b.det (D ∘ b) = D.det := by
    convert! b.det_comp D.toLinearMap b using 1
    simp only [b.det_self, mul_one]
  have H : f (D ∘ b) = D.det * f b := by
    calc
      _ = (f b • b.det) (D ∘ b) := congrArg (fun a => a (D ∘ b)) (f.eq_smul_basis_det b)
      _ = _ := by change f b * b.det (D ∘ b) = _; rw [hd, mul_comm]
  have hf (v : Fin 3 → SectionCoordinates) : f v = normalizedSectionFlux x (fun i => L (v i)) := by
    simp only [f, AlternatingMap.smul_apply, AlternatingMap.compLinearMap_apply,
      AlternatingMap.curryLeft_apply_apply, smul_eq_mul, normalizedSectionFlux,
      normalizedConstraintVolume, div_eq_mul_inv]
    rw [mul_comm]
    congr 1
  rw [hf, hf] at H
  simpa only [b, Pi.basisFun_apply, Function.comp_apply] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_chart_arrival_det_ne_zero
    {C D : SectionCoordinates → NormalizedState} {R : SectionCoordinates → SectionCoordinates}
    {y : SectionCoordinates} {τ : NormalizedState → ℝ} {t₀ : ℝ}
    (hC : DifferentiableAt ℝ C y) (hD : DifferentiableAt ℝ D (R y))
    (hR : DifferentiableAt ℝ R y) (hτ : DifferentiableAt ℝ τ (C y))
    (hp : positiveWalls (C y)) (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (ht : τ (C y) ∈ normalizedMaxDomain (C y) t₀)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (heq : (fun v => D (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (C v) t₀ (τ (C v)))) :
    (fderiv ℝ R y).det ≠ 0 := by
  let A := fun x => normalizedMaxCurve x t₀ (τ x)
  have hA := (hasFDerivAt_normalized_arrival ht hτ).differentiableAt.hasFDerivAt
  have hder : (fderiv ℝ D (R y)).comp (fderiv ℝ R y) =
      (fderiv ℝ A (C y)).comp (fderiv ℝ C y) :=
    (hD.hasFDerivAt.comp y hR.hasFDerivAt).unique ((hA.comp y hC.hasFDerivAt).congr_of_eventuallyEq heq)
  have htangent : ∀ i, normalizedConstraintDifferential (C y) (fderiv ℝ C y (Pi.single i 1)) = 0 := by
    have H := ((hasFDerivAt_stateConstraint (C y)).comp y hC.hasFDerivAt).unique
      ((hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hc)
    intro i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1)) H
  have hframe : (fun i => fderiv ℝ A (C y) (fderiv ℝ C y (Pi.single i 1))) =
      (fun i => fderiv ℝ D (R y) (fderiv ℝ R y (Pi.single i 1))) := by
    funext i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] NormalizedState => L (Pi.single i 1)) hder.symm
  have H := normalizedSectionFlux_arrival_abs hp hc.self_of_nhds ht hτ
    (fun i => fderiv ℝ C y (Pi.single i 1)) htangent
  have hvalue : D (R y) = normalizedMaxCurve (C y) t₀ (τ (C y)) := heq.self_of_nhds
  change |normalizedSectionFlux _ (fun i => fderiv ℝ A (C y) (fderiv ℝ C y (Pi.single i 1)))| = _ at H
  rw [← hvalue, hframe, normalizedSectionFlux_comp] at H
  intro hz
  rw [hz, zero_mul, abs_zero] at H
  exact (ne_of_gt (mul_pos (Real.exp_pos _) (abs_pos.mpr hflux))) H.symm

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

private theorem BianchiIX.axisWallChart_coordinates (A : NormalizedSymmetry) {h : ℝ} {x : NormalizedState}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (hp : A.map x 0 < 0) (hh : A.map x 2 = h) :
    axisWallCoordinates A x ∈ mainWallChartDomain h ∧ axisWallChart A h (axisWallCoordinates A x) = x := by
  have H := mainWallChart_coordinates ((A.positive x).mpr hpos) ((A.constraint x).trans hcon) hp hh
  refine ⟨H.1, ?_⟩
  unfold axisWallChart axisWallCoordinates
  rw [H.2, ContinuousLinearEquiv.symm_apply_apply]

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

private theorem BianchiIX.hasFDerivAt_axisWallChart (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    HasFDerivAt (axisWallChart A h) (A.map.symm.toContinuousLinearMap.comp (mainWallChartDifferential h y)) y := by
  convert! A.map.symm.hasFDerivAt.comp y (hasFDerivAt_mainWallChart hy) using 1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChartDifferential_eq (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    axisWallChartDifferential A h y = A.map.symm.toContinuousLinearMap.comp (mainWallChartDifferential h y) :=
  (hasFDerivAt_axisWallChart A hy).fderiv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_signed_flux (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    normalizedSectionFlux (axisWallChart A h y) (axisWallChartFrame A h y) = -mainWallChartDensity h y := by
  have H := A.symm.sectionFlux (mainWallChart h y) (mainWallChartFrame h y)
  have heq : axisWallChartFrame A h y = fun i => A.map.symm (mainWallChartFrame h y i) := by
    funext i
    rw [axisWallChartFrame, axisWallChartDifferential_eq A hy]
    rfl
  rw [heq]
  exact H.trans (mainWallChart_signed_flux hh hy)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.finite_axisSectionTimes (A : NormalizedSymmetry) {h ε t₀ T : ℝ} {x : NormalizedState}
    (hh : 0 < h) (hε : 0 < ε) (hpos : positiveWalls x) (hcon : stateConstraint x = 1) :
    (axisSectionTimes A h ε x t₀ T).Finite := by
  let S := (maximalNormalizedSolution x t₀).transform A
  have hd (t : ℝ) (ht : t ∈ Icc t₀ T) := hasDerivAt_normalized_components
    (S.hasDerivAt t (normalizedMaxDomain_contains_Ici hpos hcon t₀ ht.1))
  exact finite_negative_section_times isCompact_Icc
    (fun t ht => (hd t ht).2.2.1.continuousAt.continuousWithinAt)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hh hε
    (fun t ht => (hd t ht).2.2.1)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.finite_axisSectionTimes_iUnion {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {x : NormalizedState} {t₀ T : ℝ}
    (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) :
    (⋃ i, axisSectionTimes (A i) (h i) (ε i) x t₀ T).Finite :=
  Set.finite_iUnion (fun i => finite_axisSectionTimes (A i) (hh i) (hε i) hpos hcon)

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_axisWallArrival (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (ht : t ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ P : AxisWallArrival A B h k t₀, y ∈ P.source ∧ P.time (axisWallChart A h y) = t ∧
      P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      (∀ᶠ z : SectionCoordinates × ℝ in 𝓝 (y, t), z.1 ∈ P.source ∧
        z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
        (B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ↔
          P.time (axisWallChart A h z.1) = z.2)) := by
  obtain ⟨τ, R, hτ, hcτ, hcR, hRy, hlocal, hdet, _, huniq⟩ :=
    exists_axisWall_coordinate_event A B hh hk hy ht hlevel hp
  let L := (fderiv ℝ R y).toContinuousLinearEquivOfDetNeZero hdet
  have hdR : HasFDerivAt R (L : SectionCoordinates →L[ℝ] SectionCoordinates) y := by
    rw [show (L : SectionCoordinates →L[ℝ] SectionCoordinates) = fderiv ℝ R y from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact (hcR.differentiableAt (by norm_num)).hasFDerivAt
  let e := hcR.toOpenPartialHomeomorph R hdR (by norm_num)
  have hye : y ∈ e.source := hcR.mem_toOpenPartialHomeomorph_source hdR (by norm_num)
  have hgood := hlocal.and
    (((contDiffAt_axisWallChart A hy 1).continuousAt.eventually
      (hcτ.eventually (by simp))).and (hcR.eventually (by simp)))
  obtain ⟨U, hU, hUopen, hyU⟩ := mem_nhds_iff.mp hgood
  let P : AxisWallArrival A B h k t₀ := {
    source := U ∩ e.source
    time := τ
    map := R
    isOpen_source := hUopen.inter e.open_source
    source_chart := fun _ hv => (hU hv.1).1.1
    target_chart := fun _ hv => (hU hv.1).1.2.2.1
    time_mem := fun _ hv => (hU hv.1).1.2.1
    time_regular := fun _ hv => (hU hv.1).2.1
    map_regular := fun _ hv => (hU hv.1).2.2
    arrival := fun _ hv => (hU hv.1).1.2.2.2
    injOn := e.injOn.mono inter_subset_right }
  refine ⟨P, ⟨hyU, hye⟩, hτ, hRy, ?_⟩
  exact (continuousAt_fst.eventually (P.isOpen_source.mem_nhds ⟨hyU, hye⟩)).and huniq

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWall_small_target_shear {k : ℝ} {z : SectionCoordinates}
    (hk : 0 < k) (hk1 : k ≤ 1 / 8) (hz : z ∈ mainWallChartDomain k)
    (hs : |z 0| ≤ 1 / 8) (hb : Real.exp (-z 1) ≤ k / 8) (hc : Real.exp (-z 2) ≤ k / 8) :
    mainWallChart k z 0 ≤ -(15 / 16) := by
  simpa only [neg_div] using (small_section_bounds hk hk1 (Real.exp_pos _).le (Real.exp_pos _).le hb hc hs
    (mainWallChart_negative hz) (mainWallChart_constraint hz)).2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_axisWallArrivalAtlas (A B : NormalizedSymmetry) {h k t₀ : ℝ}
    (hh : 0 < h) (hk : 0 < k) : Nonempty (AxisWallArrivalAtlas A B h k t₀) := by
  classical
  let Z := axisWallArrivalRelation A B h k t₀
  by_cases hZ : Z.Nonempty
  · let : Nonempty Z := hZ.to_subtype
    have hpatch (z : Z) : ∃ (P : AxisWallArrival A B h k t₀) (V : Set (SectionCoordinates × ℝ)),
        IsOpen V ∧ z.val ∈ V ∧ ∀ q ∈ V, q.1 ∈ P.source ∧
          q.2 ∈ normalizedMaxDomain (axisWallChart A h q.1) t₀ ∧
          (B.map (normalizedMaxCurve (axisWallChart A h q.1) t₀ q.2) 2 = k ↔
            P.time (axisWallChart A h q.1) = q.2) := by
      obtain ⟨P, _, _, _, huniq⟩ := exists_axisWallArrival A B hh hk
        z.property.1 z.property.2.1 z.property.2.2.1 z.property.2.2.2
      obtain ⟨V, hV, hVopen, hzV⟩ := mem_nhds_iff.mp huniq
      exact ⟨P, V, hVopen, hzV, hV⟩
    choose P V hVopen hzV hV using hpatch
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof Z).indexed_countable_subcover V hVopen
      (by intro z hz; exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
    refine ⟨{ branch := fun n => P (f n), covers := ?_ }⟩
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hf hz)
    have H := hV (f n) z hn
    exact ⟨n, H.1, H.2.2.mp hz.2.2.1⟩
  · exact ⟨{ branch := fun _ => AxisWallArrival.empty A B h k t₀,
             covers := fun z hz => (hZ ⟨z, hz⟩).elim }⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.continuousOn_coordinateTime : ContinuousOn P.coordinateTime P.source :=
  fun y hy => ((P.time_regular y hy).continuousAt.comp
    (contDiffAt_axisWallChart A (P.source_chart hy) 1).continuousAt).continuousWithinAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.map_eq_coordinates {y : SectionCoordinates} (hy : y ∈ P.source) :
    P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ (P.coordinateTime y)) := by
  rw [coordinateTime, ← P.arrival y hy, axisWallCoordinates_chart]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.mem_relation {y : SectionCoordinates} (hy : y ∈ P.source) :
    (y, P.coordinateTime y) ∈ axisWallArrivalRelation A B h k t₀ := by
  refine ⟨P.source_chart hy, P.time_mem y hy, ?_, ?_⟩
  · rw [coordinateTime, ← P.arrival y hy, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · rw [coordinateTime, ← P.arrival y hy, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative (P.target_chart hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.AxisWallArrivalAtlas.mem_relation_iff {A B : NormalizedSymmetry} {h k t₀ : ℝ}
    (C : AxisWallArrivalAtlas A B h k t₀) (y : SectionCoordinates) (t : ℝ) :
    (y, t) ∈ axisWallArrivalRelation A B h k t₀ ↔
      ∃ n, y ∈ (C.branch n).source ∧ (C.branch n).coordinateTime y = t := by
  constructor
  · exact C.covers (y, t)
  · rintro ⟨n, hy, ht⟩
    rw [← ht]
    exact (C.branch n).mem_relation hy

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_axisWallAtlasFamily {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    {h t₀ : ℝ} {k : ι → ℝ} (hh : 0 < h) (hk : ∀ i, 0 < k i) :
    Nonempty (AxisWallAtlasFamily A B h k t₀) :=
  ⟨fun i => Classical.choice (exists_axisWallArrivalAtlas A (B i) hh (hk i))⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measurableSet_eligible {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : MeasurableSet (P.eligible E I) := by
  have ht := P.continuousOn_coordinateTime.domRestrict.measurable
  have hm := (show ContinuousOn P.map P.source from
    fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt).domRestrict.measurable
  have H := P.isOpen_source.measurableSet.subtype_image ((hI.preimage ht).inter (hE.preimage hm))
  convert! H using 1
  ext y
  simp only [eligible, mem_ofPred_eq, mem_image, mem_inter_iff, mem_preimage, domRestrict_apply]
  aesop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.delay_of_mem {E : Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hy : y ∈ P.eligible E I) : P.delay E I y = ENNReal.ofReal (P.coordinateTime y - t₀) := by
  classical
  simp only [delay, piecewise_eq_of_mem _ _ _ hy]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measurable_delay {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : Measurable (P.delay E I) := by
  classical
  have hc : ContinuousOn (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (P.eligible E I) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((P.continuousOn_coordinateTime.mono (fun _ hy => hy.1)).sub continuousOn_const)
  exact hc.measurable_piecewise continuousOn_const (P.measurableSet_eligible hE hI)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.hittingDomain_eq_iUnion (E : ι → Set SectionCoordinates) (I : Set ℝ) :
    axisFamilyHittingDomain A B h k t₀ E I = ⋃ i, ⋃ n, ((C i).branch n).eligible (E i) I := by
  ext y
  constructor
  · rintro ⟨t, ht, i, hrel, hE⟩
    obtain ⟨n, hy, htime⟩ := ((C i).mem_relation_iff y t).mp hrel
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨n, hy, ?_, ?_⟩⟩
    · rwa [htime]
    · rwa [((C i).branch n).map_eq_coordinates hy, htime]
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    refine ⟨((C i).branch n).coordinateTime y, hn.2.1, i, ((C i).branch n).mem_relation hn.1, ?_⟩
    rw [← ((C i).branch n).map_eq_coordinates hn.1]
    exact hn.2.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

include C in
private theorem BianchiIX.AxisWallAtlasFamily.measurableSet_hittingDomain [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    MeasurableSet (axisFamilyHittingDomain A B h k t₀ E I) := by
  rw [C.hittingDomain_eq_iUnion E I]
  exact MeasurableSet.iUnion (fun i => MeasurableSet.iUnion
    (fun n => ((C i).branch n).measurableSet_eligible (hE i) hI))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.measurable_firstDelay [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) : Measurable (C.firstDelay E I) :=
  Measurable.iInf (fun i => Measurable.iInf (fun n => ((C i).branch n).measurable_delay (hE i) hI))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_axisFamilyHittingDomain {ι : Type*} [Countable ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k : ι → ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    MeasurableSet (axisFamilyHittingDomain A B h k t₀ E I) := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  exact C.measurableSet_hittingDomain hE hI

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

private theorem BianchiIX.axisWallArrivalRelation_chart (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : (y, t) ∈ axisWallArrivalRelation A B h k t₀) :
    axisWallChart B k (axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t)) =
      normalizedMaxCurve (axisWallChart A h y) t₀ t := by
  have hp := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical
    (axisWallChart_positive A hh y) (axisWallChart_constraint A hy.1) hy.2.1
  convert! (axisWallChart_coordinates B hp.1 hp.2 hy.2.2.2 hy.2.2.1).2 using 1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisFamilyHittingTimes_source {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
    {h t₀ t : ℝ} {k : ι → ℝ} {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (ht : t ∈ axisFamilyHittingTimes A B h k t₀ E I y) : y ∈ mainWallChartDomain h := by
  obtain ⟨_, _, hrel, _⟩ := ht
  exact hrel.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.finite_axisFamilyHittingTimes {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ T : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hy : y ∈ mainWallChartDomain h)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i) :
    (axisFamilyHittingTimes A B h k t₀ E I y ∩ Icc t₀ T).Finite := by
  have hpos := axisWallChart_positive A hh y
  have hcon := axisWallChart_constraint A hy
  apply (finite_axisSectionTimes_iUnion B hk hε hpos hcon).subset
  rintro t ⟨⟨_, i, hrel, hE⟩, htK⟩
  have hphys := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical hpos hcon hrel.2.1
  have hc := axisWallChart_coordinates (B i) hphys.1 hphys.2 hrel.2.2.2 hrel.2.2.1
  have heq : mainWallChart (k i)
      (axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart A h y) t₀ t)) =
      (B i).map (normalizedMaxCurve (axisWallChart A h y) t₀ t) := by
    have H := congrArg (B i).map hc.2
    simp only [axisWallChart, ContinuousLinearEquiv.apply_symm_apply] at H
    convert! H using 1
  have H := hbound i _ hE
  rw [heq] at H
  exact mem_iUnion.mpr ⟨i, htK, hrel.2.2.1, H⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_axisFamily_first_time {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    ∃ t, IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t := by
  obtain ⟨b, hb⟩ := hy
  have hsource : y ∈ mainWallChartDomain h := by
    obtain ⟨i, hi, _⟩ := hb.2
    exact hi.1
  have hfinite := finite_axisFamilyHittingTimes A B (t₀ := t₀) (T := b) (I := I) hh hk hε hsource hbound
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image
    (axisFamilyHittingTimes A B h k t₀ E I y ∩ Icc t₀ b) id hfinite
      ⟨b, hb, hI hb.1, le_rfl⟩
  refine ⟨t, ht.1, fun u hu => ?_⟩
  by_cases hub : u ≤ b
  · exact hmin u ⟨hu, hI hu.1, hub⟩
  · exact ht.2.2.trans (le_of_not_ge hub)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstDelay_of_isLeast {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (ht : IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t) :
    C.firstDelay E I y = ENNReal.ofReal (t - t₀) ∧
      ∃ i n, y ∈ ((C i).branch n).eligible (E i) I ∧ ((C i).branch n).coordinateTime y = t := by
  classical
  obtain ⟨i, hrel, hE⟩ := ht.1.2
  obtain ⟨n, hyn, hn⟩ := ((C i).mem_relation_iff y t).mp hrel
  have heligible : y ∈ ((C i).branch n).eligible (E i) I := by
    refine ⟨hyn, ?_, ?_⟩
    · rw [hn]
      exact ht.1.1
    · rwa [((C i).branch n).map_eq_coordinates hyn, hn]
  refine ⟨le_antisymm ?_ ?_, i, n, heligible, hn⟩
  · calc
      C.firstDelay E I y ≤ ((C i).branch n).delay (E i) I y := iInf_le_of_le i (iInf_le _ n)
      _ = ENNReal.ofReal (t - t₀) := by rw [((C i).branch n).delay_of_mem heligible, hn]
  · apply le_iInf
    intro j
    apply le_iInf
    intro m
    by_cases hym : y ∈ ((C j).branch m).eligible (E j) I
    · rw [((C j).branch m).delay_of_mem hym]
      apply ENNReal.ofReal_le_ofReal
      apply sub_le_sub_right
      apply ht.2
      refine ⟨hym.2.1, j, ((C j).branch m).mem_relation hym.1, ?_⟩
      rw [← ((C j).branch m).map_eq_coordinates hym.1]
      exact hym.2.2
    · simp [AxisWallArrival.delay, hym]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.measurable_firstTime [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) : Measurable (C.firstTime E I) :=
  measurable_const.add (C.measurable_firstDelay hE hI).ennreal_toReal

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstTime_of_isLeast {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    {t : ℝ} (hI : I ⊆ Ici t₀) (ht : IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t) :
    C.firstTime E I y = t := by
  rw [firstTime, (C.firstDelay_of_isLeast ht).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hI ht.1.1))]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstTime_isLeast [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (C.firstTime E I y) := by
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hy
  rwa [C.firstTime_of_isLeast hI ht]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_measurable_axisFamily_firstTime {ι : Type*} [Finite ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hImeas : MeasurableSet I) :
    ∃ τ : SectionCoordinates → ℝ, Measurable τ ∧
      ∀ y ∈ axisFamilyHittingDomain A B h k t₀ E I,
        IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (τ y) := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  exact ⟨C.firstTime E I, C.measurable_firstTime hE hImeas,
    fun _ hy => C.firstTime_isLeast hh hk hε hI hbound hy⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

@[simp] private theorem BianchiIX.cumulativeReturnTime_zero {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (y : X) :
    cumulativeReturnTime R τ t₀ 0 y = t₀ := by simp [cumulativeReturnTime]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.cumulativeReturnTime_succ {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (n : ℕ) (y : X) :
    cumulativeReturnTime R τ t₀ (n + 1) y = cumulativeReturnTime R τ t₀ n y + τ (R^[n] y) - t₀ := by
  simp only [cumulativeReturnTime, Finset.sum_range_succ]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_axisFamilyReturnDomain {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry) {k : ι → ℝ} {t₀ : ℝ}
    {E : ι → Set SectionCoordinates} (hk : ∀ i, 0 < k i) (hE : ∀ i, MeasurableSet (E i)) :
    MeasurableSet (axisFamilyReturnDomain B k t₀ E) := by
  have heq : axisFamilyReturnDomain B k t₀ E = ⋃ i,
      {i} ×ˢ (E i ∩ axisFamilyHittingDomain (B i) B (k i) k t₀ E (Ioi t₀)) := by
    ext z
    simp [axisFamilyReturnDomain, axisFamilyReturnTimes, axisFamilyHittingDomain]
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod
    ((hE i).inter (measurableSet_axisFamilyHittingDomain (B i) B (hk i) hk hE measurableSet_Ioi)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.normalizedSectionFlux_eq_zero_on_taub {x : NormalizedState}
    {v : Fin 3 → NormalizedState} (hs : x 1 = 0) (hw : x 3 = x 4)
    (hv : ∀ i, v i 1 = 0) : normalizedSectionFlux x v = 0 := by
  unfold normalizedSectionFlux normalizedConstraintVolume normalizedAmbientVolume
  rw [Pi.basisFun_det_apply]
  have hdet : (Matrix.of (Fin.cons ((1 / 2 : ℝ) • x) (Fin.cons (normalizedField x) v))).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero 1
    intro j
    fin_cases j
    · simp [hs]
    · simp [normalizedField, shearMinus, hs, hw]
    · exact hv 0
    · exact hv 1
    · exact hv 2
  rw [hdet, zero_div]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_taub_subspace_section
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧ normalizedTaubRadiusSq (C y) = 0} = 0 := by
  have hcoords {y : SectionCoordinates} (hy : normalizedTaubRadiusSq (C y) = 0) :
      C y 1 = 0 ∧ C y 3 = C y 4 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hy
    constructor
    · nlinarith only [hy, sq_nonneg (C y 3 - C y 4)]
    · nlinarith only [hy, sq_nonneg (C y 1)]
  apply volume_regular_scalar_level (g := fun y => C y 1)
  · intro y hy
    exact (contDiffAt_pi.mp (hC y hy.1)) 1
  · exact fun _ hy => (hcoords hy.2).1
  · intro y hy
    have hd := ((hasFDerivAt_apply 1 (C y)).comp y
      ((hC y hy.1).differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    by_contra! hn
    apply hflux y hy.1
    exact normalizedSectionFlux_eq_zero_on_taub (hcoords hy.2).1 (hcoords hy.2).2 hn

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_axis_taub_subspace_section (A : NormalizedSymmetry)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧ normalizedTaubRadiusSq (A.map (C y)) = 0} = 0 := by
  apply volume_taub_subspace_section
    (fun y hy => A.map.contDiff.contDiffAt.comp y (hC y hy))
  intro y hy
  have hd := (A.map.hasFDerivAt.comp y ((hC y hy).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd ⊢
  rw [hd]
  change normalizedSectionFlux (A.map (C y))
    (fun i => A.map (fderiv ℝ C y (Pi.single i 1))) ≠ 0
  rw [A.sectionFlux]
  exact hflux y hy

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.ae_primaryAxis_taubRadiusSq_pos
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      ∀ i : Fin 3, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map (C y)) := by
  have H (i : Fin 3) : ∀ᵐ y ∂(volume.withDensity ρ),
      ¬(y ∈ U ∧ normalizedTaubRadiusSq ((primaryAxisFrame i).map (C y)) = 0) := by
    rw [ae_iff]
    simpa only [not_not] using withDensity_absolutelyContinuous volume ρ
      (volume_axis_taub_subspace_section (primaryAxisFrame i) hC hflux)
  filter_upwards [ae_all_iff.mpr H] with y hy hyU i
  exact lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _) (fun hz => hy i ⟨hyU, hz.symm⟩)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallChartDomain_of_negative {h : ℝ} {y : SectionCoordinates}
    (hy : mainWallChart h y 0 < 0) : y ∈ mainWallChartDomain h := by
  change -Real.sqrt (mainWallRadicand h y) < 0 at hy
  exact Real.sqrt_pos.mp (by linarith)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisFamilySection_chart_of_shear {ι : Type*} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    {z : ι × SectionCoordinates} (hz : z ∈ axisFamilySection E) : z.2 ∈ mainWallChartDomain (k z.1) :=
  mainWallChartDomain_of_negative ((hbound z.1 z.2 hz).trans_lt (neg_neg_of_pos (hε z.1)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_measurable_axisFamily_returnTime {ι : Type*} [Finite ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) :
    ∃ τ : ι × SectionCoordinates → ℝ, Measurable τ ∧
      ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z) := by
  classical
  have hlocal (i : ι) := exists_measurable_axisFamily_firstTime (B i) B (t₀ := t₀)
    (hk i) hk hε (show Ioi t₀ ⊆ Ici t₀ from fun x hx => show t₀ ≤ x from le_of_lt hx)
    hbound hE measurableSet_Ioi
  choose τ hτ hfirst using hlocal
  exact ⟨fun z => τ z.1 z.2, measurable_from_prod_countable_right hτ, fun z hz => hfirst z.1 z.2 hz.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisFamily_firstReturn_eq_at_returnTime {ι : Type*} {B : ι → NormalizedSymmetry}
    {k : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    {R : ι × SectionCoordinates → ι × SectionCoordinates} {τ : ι × SectionCoordinates → ℝ}
    (hfirst : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    {z : ι × SectionCoordinates} (hz : z ∈ axisFamilyReturnDomain B k t₀ E) :
    axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z) := by
  obtain ⟨t, ht, heq⟩ := hfirst z hz
  rwa [ht.unique (hτ z hz)] at heq

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_axisFamily_firstReturn_capture {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ R : ι × SectionCoordinates → ι × SectionCoordinates,
      Measurable R ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      ∀ F, MeasurableSet F → axisFamilyMeasure k F ≠ ∞ →
        axisFamilyMeasure k (permanentFailure R (axisFamilyReturnDomain B k t₀ E) F) = 0 ∧
        ∀ᵐ z ∂axisFamilyMeasure k, (∀ n : ℕ, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) →
          ∃ n : ℕ, R^[n] z ∉ F := by
  obtain ⟨R, j, hR, hj, hinj, hfirst, hexpand, hchange⟩ :=
    exists_axisFamily_firstReturn B (t₀ := t₀) hk hε hbound hE hcharts
  have hD := measurableSet_axisFamilyReturnDomain B (t₀ := t₀) hk hE
  have hexpand' := fun z hz => (hexpand z hz).1
  have hchange' := fun S hS hSD => (hchange S hS hSD).2
  exact ⟨R, hR, hinj, hfirst, fun F hF hfinite =>
    ⟨permanentFailure_null hR hD hF hfinite hj hexpand' hchange',
      ae_eventually_leaves_failure hR hD hF hfinite hj hexpand' hchange'⟩⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_return_iterate_state (hk : ∀ i, 0 < k i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hz : z.2 ∈ mainWallChartDomain (k z.1)) (n : ℕ)
    (hvalid : ∀ i < n, R^[i] z ∈ axisFamilyReturnDomain B k t₀ E) :
    t₀ ≤ cumulativeReturnTime R τ t₀ n z ∧
      axisFamilyChart B k (R^[n] z) = normalizedMaxCurve (axisFamilyChart B k z) t₀
        (cumulativeReturnTime R τ t₀ n z) := by
  induction n with
  | zero => simp [normalizedMaxCurve_initial]
  | succ n ih =>
    obtain ⟨hle, hstate⟩ := ih (fun i hi => hvalid i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hn := hvalid n (Nat.lt_succ_self n)
    have hpos : t₀ < τ (R^[n] z) := (hτ _ hn).1.1
    have hnext : t₀ ≤ cumulativeReturnTime R τ t₀ (n + 1) z := by
      rw [cumulativeReturnTime_succ]
      linarith
    refine ⟨hnext, ?_⟩
    have hstart : t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) ∈
        normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
      convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀
        (show t₀ ≤ t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) by linarith) using 1
    have hend : τ (R^[n] z) + (cumulativeReturnTime R τ t₀ n z - t₀) ∈
        normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
      convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀
        (show t₀ ≤ τ (R^[n] z) + (cumulativeReturnTime R τ t₀ n z - t₀) by linarith) using 1
    have H := normalizedMaxCurve_shift hstart hend
    rw [show t₀ + (cumulativeReturnTime R τ t₀ n z - t₀) =
      cumulativeReturnTime R τ t₀ n z by ring, ← hstate] at H
    rw [Function.iterate_succ_apply', hR _ hn, H, cumulativeReturnTime_succ]
    congr 1
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_return_times_strictMono
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) :
    StrictMono (fun n => cumulativeReturnTime R τ t₀ n z) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hpos : t₀ < τ (R^[n] z) := (hτ _ (hvalid n)).1.1
  rw [cumulativeReturnTime_succ]
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_return_time_mem (hk : ∀ i, 0 < k i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    {z : ι × SectionCoordinates} (hvalid : ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E)
    {n : ℕ} (hn : 0 < n) : cumulativeReturnTime R τ t₀ n z ∈ axisFamilyReturnTimes B k t₀ E z := by
  have hz : z.2 ∈ mainWallChartDomain (k z.1) := by
    simpa using axisFamilyHittingTimes_source (hτ _ (hvalid 0)).1
  have hpos : t₀ < cumulativeReturnTime R τ t₀ n z := by
    simpa using axisFamily_return_times_strictMono hτ hvalid hn
  have hstate := (axisFamily_return_iterate_state hk hτ hR hz n (fun i _ => hvalid i)).2
  have hstate' : axisWallChart (B (R^[n] z).1) (k (R^[n] z).1) (R^[n] z).2 =
      normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ (cumulativeReturnTime R τ t₀ n z) := by
    convert! hstate using 1
  have hnchart := axisFamilyHittingTimes_source (hτ _ (hvalid n)).1
  refine ⟨hpos, (R^[n] z).1, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ hpos.le
  · rw [← hstate', axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · rw [← hstate', axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    exact mainWallChart_negative hnchart
  · rw [← hstate', axisWallCoordinates_chart]
    exact (hvalid n).1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_hittingTimes_after_time (hk : ∀ i, 0 < k i) {z w : ι × SectionCoordinates} {s t : ℝ}
    (hz : z.2 ∈ mainWallChartDomain (k z.1)) (hw : w.2 ∈ mainWallChartDomain (k w.1)) (hs : t₀ ≤ s)
    (hstate : axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ s) (ht : s < t) :
    t ∈ axisFamilyReturnTimes B k t₀ E z ↔ t₀ + (t - s) ∈ axisFamilyReturnTimes B k t₀ E w := by
  have hu : t₀ + (s - t₀) ∈ normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
    convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ (show t₀ ≤ t₀ + (s - t₀) by linarith) using 1
  have hv : (t₀ + (t - s)) + (s - t₀) ∈ normalizedMaxDomain (axisFamilyChart B k z) t₀ := by
    convert! normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
      (axisWallChart_constraint (B z.1) hz) t₀ (show t₀ ≤ (t₀ + (t - s)) + (s - t₀) by linarith) using 1
  have H := normalizedMaxCurve_shift hu hv
  rw [show t₀ + (s - t₀) = s by ring, ← hstate,
    show (t₀ + (t - s)) + (s - t₀) = t by ring] at H
  have H' : normalizedMaxCurve (axisWallChart (B w.1) (k w.1) w.2) t₀ (t₀ + (t - s)) =
      normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t := by convert! H using 1
  constructor
  · rintro ⟨_, i, hrel, hE⟩
    refine ⟨show t₀ < t₀ + (t - s) by linarith, i, ⟨hw, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B w.1) (hk w.1) w.2)
        (axisWallChart_constraint (B w.1) hw) t₀ (show t₀ ≤ t₀ + (t - s) by linarith)
    · rw [H']; exact hrel.2.2.1
    · rw [H']; exact hrel.2.2.2
    · rw [H']; exact hE
  · rintro ⟨_, i, hrel, hE⟩
    refine ⟨hs.trans_lt ht, i, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀ (hs.trans ht.le)
    · rw [← H']; exact hrel.2.2.1
    · rw [← H']; exact hrel.2.2.2
    · rw [← H']; exact hE

end
end

section
noncomputable section
open BianchiIX
open Set Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_returnTimes_eq_physical_hits (hk : ∀ i, 0 < k i)
    (hchart : ∀ i, E i ⊆ mainWallChartDomain (k i)) (z : ι × SectionCoordinates) :
    axisFamilyReturnTimes B k t₀ E z =
      {t | t₀ < t ∧ z.2 ∈ mainWallChartDomain (k z.1) ∧ ∃ w ∈ axisFamilySection E,
        axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ t} := by
  ext t
  constructor
  · rintro ⟨ht, i, hrel, hE⟩
    refine ⟨ht, hrel.1,
      (i, axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t)), hE, ?_⟩
    convert! axisWallArrivalRelation_chart (B z.1) (B i) (hk z.1) hrel using 1
  · rintro ⟨ht, hz, w, hw, hstate⟩
    have H : axisWallChart (B w.1) (k w.1) w.2 =
        normalizedMaxCurve (axisWallChart (B z.1) (k z.1) z.2) t₀ t := by convert! hstate using 1
    refine ⟨ht, w.1, ⟨hz, ?_, ?_, ?_⟩, ?_⟩
    · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B z.1) (hk z.1) z.2)
        (axisWallChart_constraint (B z.1) hz) t₀ ht.le
    · rw [← H, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · rw [← H, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      exact mainWallChart_negative (hchart w.1 hw)
    · rw [← H, axisWallCoordinates_chart]
      exact hw

end
end

section
noncomputable section
open BianchiIX
open Set Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_infinite_hittingTimes_iff_unbounded [Finite ι] {ε : ι → ℝ}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    {z : ι × SectionCoordinates} (hz : z.2 ∈ mainWallChartDomain (k z.1)) :
    (axisFamilyReturnTimes B k t₀ E z).Infinite ↔ ¬ BddAbove (axisFamilyReturnTimes B k t₀ E z) := by
  constructor
  · intro hinfinite hbounded
    obtain ⟨T, hT⟩ := hbounded
    have hfinite := finite_axisFamilyHittingTimes (B z.1) B (t₀ := t₀) (T := T) (I := Ioi t₀)
      (hk z.1) hk hε hz hbound
    exact hinfinite (hfinite.subset (fun t ht => ⟨ht, le_of_lt ht.1, hT ht⟩))
  · exact infinite_of_not_bddAbove

end
end

section
noncomputable section
open BianchiIX
open Set Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_return_iterates_of_unbounded_hits (hk : ∀ i, 0 < k i)
    (hchart : ∀ i, E i ⊆ mainWallChartDomain (k i))
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    (htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E))
    {z : ι × SectionCoordinates} (hzE : z ∈ axisFamilySection E)
    (hunbounded : ¬ BddAbove (axisFamilyReturnTimes B k t₀ E z)) :
    ∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E := by
  have hz := hchart z.1 hzE
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hstate := axisFamily_return_iterate_state hk hτ hR hz n ih
    have hmember : R^[n] z ∈ axisFamilySection E := by
      cases n with
      | zero => simpa using hzE
      | succ m =>
        rw [Function.iterate_succ_apply']
        exact htarget (ih m (Nat.lt_succ_self m))
    have hw := hchart (R^[n] z).1 hmember
    obtain ⟨t, ht, hnt⟩ := not_bddAbove_iff.mp hunbounded (cumulativeReturnTime R τ t₀ n z)
    have hhit := (axisFamily_hittingTimes_after_time hk hz hw hstate.1 hstate.2 hnt).mp ht
    exact ⟨hmember, ⟨t₀ + (t - cumulativeReturnTime R τ t₀ n z), hhit⟩⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
variable {ι : Type*} {B : ι → NormalizedSymmetry} {k : ι → ℝ} {t₀ : ℝ}
  {E : ι → Set SectionCoordinates} {R : ι × SectionCoordinates → ι × SectionCoordinates}
  {τ : ι × SectionCoordinates → ℝ}

private theorem BianchiIX.axisFamily_return_iterates_iff_infinite_hits [Finite ι] (hk : ∀ i, 0 < k i) {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hτ : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, IsLeast (axisFamilyReturnTimes B k t₀ E z) (τ z))
    (hR : ∀ z ∈ axisFamilyReturnDomain B k t₀ E,
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ (τ z))
    (htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E))
    {z : ι × SectionCoordinates} (hzE : z ∈ axisFamilySection E) :
    (∀ n, R^[n] z ∈ axisFamilyReturnDomain B k t₀ E) ↔ (axisFamilyReturnTimes B k t₀ E z).Infinite := by
  constructor
  · intro hvalid
    have hm := axisFamily_return_times_strictMono hτ hvalid
    apply (infinite_range_of_injective (f := fun n => cumulativeReturnTime R τ t₀ (n + 1) z)
      (fun _ _ heq => Nat.add_right_cancel (hm.injective heq))).mono
    rintro _ ⟨n, rfl⟩
    exact axisFamily_return_time_mem hk hτ hR hvalid (Nat.zero_lt_succ n)
  · intro hinfinite
    have hchart (i : ι) : E i ⊆ mainWallChartDomain (k i) := fun _ hy =>
      axisFamilySection_chart_of_shear hε hbound (z := (i, _)) hy
    exact axisFamily_return_iterates_of_unbounded_hits hk hchart hτ hR htarget hzE
      ((axisFamily_infinite_hittingTimes_iff_unbounded hk hε hbound (hchart z.1 hzE)).mp hinfinite)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.ae_axisFamily_physical_capture {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates} {F : Set (ι × SectionCoordinates)}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ y ∈ E i, mainWallChart (k i) y 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure k F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure k, z ∈ axisFamilyInfiniteReturns B k t₀ E →
      ∃ t ≥ t₀, ∃ w ∈ axisFamilySection E \ F,
        axisFamilyChart B k w = normalizedMaxCurve (axisFamilyChart B k z) t₀ t := by
  obtain ⟨R, _, _, hfirst, hcapture⟩ := exists_axisFamily_firstReturn_capture B (t₀ := t₀) hk hε hbound hE hcharts
  obtain ⟨τ, _, hτ⟩ := exists_measurable_axisFamily_returnTime B (t₀ := t₀) hk hε hbound hE
  have hRtime := fun z hz => axisFamily_firstReturn_eq_at_returnTime
    (fun w hw => let ⟨t, ht, hstate, _⟩ := hfirst w hw; ⟨t, ht, hstate⟩) hτ (z := z) hz
  have htarget : MapsTo R (axisFamilyReturnDomain B k t₀ E) (axisFamilySection E) := by
    intro z hz
    obtain ⟨_, _, _, htarget⟩ := hfirst z hz
    exact htarget
  filter_upwards [(hcapture F hF hfinite).2] with z hz hrec
  have hvalid := (axisFamily_return_iterates_iff_infinite_hits hk hε hbound hτ hRtime htarget hrec.1).mpr hrec.2
  obtain ⟨n, hn⟩ := hz hvalid
  have hzchart := axisFamilySection_chart_of_shear hε hbound hrec.1
  obtain ⟨hle, hstate⟩ := axisFamily_return_iterate_state hk hτ hRtime hzchart n (fun i _ => hvalid i)
  exact ⟨cumulativeReturnTime R τ t₀ n z, hle, R^[n] z, ⟨(hvalid n).1, hn⟩, hstate⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.ae_smallAxis_physical_capture {h t₀ : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) t₀ E →
        ∃ t ≥ t₀, ∃ w ∈ axisFamilySection E \ F,
          axisFamilyChart primaryAxisFrame (fun _ => h) w =
            normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) t₀ t := by
  have hbound (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) : mainWallChart h y 0 ≤ -(15 / 16) :=
    mainWall_small_target_shear hh hh1 (hsmall i y hy).1 (hsmall i y hy).2.1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  have hdom (i : Fin 3) : E i ⊆ dominantWallChartDomain h := fun y hy =>
    mem_dominantWallChartDomain_of_small hh (hsmall i y hy).1
      (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2
  exact ae_axisFamily_physical_capture primaryAxisFrame (fun _ => hh)
    (fun _ => by norm_num : ∀ _ : Fin 3, (0 : ℝ) < 15 / 16) hbound hE (primaryAxisChart_injOn hdom) hF hfinite

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.ae_smallAxis_success_hitting {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
        axisFamilyChart primaryAxisFrame (fun _ => h) z ∈
          globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) := by
  filter_upwards [ae_smallAxis_physical_capture (t₀ := 0) hh hh1 hE hsmall hF hfinite] with z hz hrec
  obtain ⟨t, ht, w, hw, heq⟩ := hz hrec
  have hpos := axisWallChart_positive (primaryAxisFrame z.1) hh z.2
  have hcon := axisWallChart_constraint (primaryAxisFrame z.1) (hsmall z.1 z.2 hrec.1).1
  exact ⟨t, ht, normalizedMaxDomain_contains_Ici hpos hcon 0 ht, w.1, w.2, hw, heq⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.unit_active_wall_clock_ne_zero {x : NormalizedState} (hv : toProjectiveState x 2 = 1) :
    1 + x 0 ≠ 0 := by
  intro hzero
  change projectiveCoord (x 0) (x 3) = 1 at hv
  simp only [projectiveCoord, hzero, div_zero] at hv
  norm_num at hv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreSectionEmbedding_coordinates {z : ProjectiveState} (hz : z 2 = 1) :
    coreSectionEmbedding (coreSectionCoordinates z) = z := by
  ext i
  fin_cases i <;> simp [coreSectionEmbedding, coreSectionCoordinates, hz]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreSectionChart_reconstruct {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : projectiveActiveWall x = 1) :
    coreSectionChart (normalizedCoreCoordinates x) = x := by
  rw [coreSectionChart, normalizedCoreCoordinates, coreSectionEmbedding_coordinates hv]
  exact fromProjectiveState_toProjectiveState (unit_active_wall_clock_ne_zero hv) hc

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedCoreCoordinates (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n normalizedCoreCoordinates x :=
  (contDiff_coreSectionCoordinates n).contDiffAt.comp x (contDiffAt_toProjectiveState n hA)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreSectionChart_coordinates (n : WithTop ℕ∞) {x : NormalizedState}
    (hc : stateConstraint x = 1) (hv : projectiveActiveWall x = 1) :
    ContDiffAt ℝ n coreSectionChart (normalizedCoreCoordinates x) := by
  have hA := unit_active_wall_clock_ne_zero hv
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    intro hzero
    have H := projective_inverse_scale hA hc
    change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
    rw [hzero, div_zero] at H
    exact hA H.symm
  have hD' : projectiveStateDenom (coreSectionEmbedding (normalizedCoreCoordinates x)) ≠ 0 := by
    simpa only [normalizedCoreCoordinates, coreSectionEmbedding_coordinates hv] using hD
  exact (contDiffAt_fromProjectiveState n hD').comp _ (contDiff_coreSectionEmbedding n).contDiffAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_transverse_core_arrival
    {C : SectionCoordinates → NormalizedState} {y : SectionCoordinates} {t₀ t : ℝ}
    (hC : ContDiffAt ℝ 1 C y) (hp : positiveWalls (C y))
    (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ht : t ∈ normalizedMaxDomain (C y) t₀)
    (hv : projectiveActiveWall (normalizedMaxCurve (C y) t₀ t) = 1)
    (htrans : normalizedEventRate projectiveActiveWall (C y) t₀ t ≠ 0) :
    ∃ R : SectionCoordinates → SectionCoordinates, ContDiffAt ℝ 1 R y ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      ∀ᶠ p : SectionCoordinates × ℝ in 𝓝 (y, t),
        projectiveActiveWall (normalizedMaxCurve (C p.1) t₀ p.2) = 1 →
          R p.1 = normalizedCoreCoordinates (normalizedMaxCurve (C p.1) t₀ p.2) := by
  have hA := unit_active_wall_clock_ne_zero hv
  obtain ⟨τ, hτ, hcτ, _, hhit, huniq, hcMap, _⟩ :=
    exists_normalized_event ht (contDiffAt_projectiveActiveWall 1 hA) htrans
  let F := fun v => normalizedMaxCurve (C v) t₀ (τ (C v))
  let R := fun v => normalizedCoreCoordinates (F v)
  have hF : ContDiffAt ℝ 1 F y := hcMap.comp y hC
  have hFy : F y = normalizedMaxCurve (C y) t₀ t := by simp only [F, hτ]
  have hR : ContDiffAt ℝ 1 R y :=
    (contDiffAt_normalizedCoreCoordinates 1 (by simpa only [hFy] using hA)).comp y hF
  have hcf : stateConstraint (F y) = 1 := by
    rw [hFy, normalizedMaxCurve_constraint ht, hc.self_of_nhds]
  have hvf : projectiveActiveWall (F y) = 1 := by rw [hFy]; exact hv
  have heq : (fun v => coreSectionChart (R v)) =ᶠ[𝓝 y] F := by
    filter_upwards [hc, hC.continuousAt.eventually hhit] with v hcv htv
    exact coreSectionChart_reconstruct ((normalizedMaxCurve_constraint htv.1).trans hcv)
      (htv.2.trans hv)
  have hdet : (fderiv ℝ R y).det ≠ 0 :=
    normalized_chart_arrival_det_ne_zero (hC.differentiableAt (by norm_num))
      ((contDiffAt_coreSectionChart_coordinates 1 hcf hvf).differentiableAt (by norm_num))
      (hR.differentiableAt (by norm_num)) (hcτ.differentiableAt (by norm_num)) hp hc
      (by rw [hτ]; exact ht) hflux heq
  refine ⟨R, hR, hdet, ?_⟩
  have hpair : Tendsto (fun p : SectionCoordinates × ℝ => (C p.1, p.2))
      (𝓝 (y, t)) (𝓝 (C y, t)) :=
    (hC.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [hpair.eventually huniq] with p hp hlevel
  have htime : τ (C p.1) = p.2 := hp.2.mp (hlevel.trans hv.symm)
  simp only [R, F, htime]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.volume_transverseCoreHittingDomain
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates} {t₀ : ℝ}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hZ : volume Z = 0) :
    volume (U ∩ transverseCoreHittingDomain C t₀ Z) = 0 := by
  let S : Set (SectionCoordinates × ℝ) := {p | p.1 ∈ U ∧
    p.2 ∈ normalizedMaxDomain (C p.1) t₀ ∧
    projectiveActiveWall (normalizedMaxCurve (C p.1) t₀ p.2) = 1 ∧
    normalizedEventRate projectiveActiveWall (C p.1) t₀ p.2 ≠ 0 ∧
    normalizedCoreCoordinates (normalizedMaxCurve (C p.1) t₀ p.2) ∈ Z}
  have hnull : volume (Prod.fst '' S) = 0 := by
    apply volume_fst_image_eq_zero_of_local_null
    intro p hpS
    obtain ⟨R, hR, hdet, hnear⟩ := exists_transverse_core_arrival (hC p.1 hpS.1)
      (hp p.1 hpS.1) ((show ∀ᶠ y in 𝓝 p.1, y ∈ U from hU.mem_nhds hpS.1).mono
        fun y hy => hc y hy)
      (hflux p.1 hpS.1) hpS.2.1 hpS.2.2.1 hpS.2.2.2.1
    obtain ⟨W, hWo, hpW, hWnull⟩ := exists_local_null_preimage hR hdet
    have hfst : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p, q.1 ∈ W :=
      continuousAt_fst.eventually (hWo.mem_nhds hpW)
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (hnear.and hfst)
    refine ⟨V, hVo, hpV, W ∩ R ⁻¹' Z, hWnull Z hZ, ?_⟩
    intro q hq
    refine ⟨(hV hq.2).2, ?_⟩
    change R q.1 ∈ Z
    rw [(hV hq.2).1 hq.1.2.2.1]
    exact hq.1.2.2.2.2
  apply measure_mono_null _ hnull
  rintro y ⟨hy, t, ht⟩
  exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.volume_axis_transverseCoreHittingDomain
    (A : NormalizedSymmetry) {C : SectionCoordinates → NormalizedState}
    {U : Set SectionCoordinates} {t₀ : ℝ}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hZ : volume Z = 0) :
    volume (U ∩ transverseCoreHittingDomain (fun y => A.map (C y)) t₀ Z) = 0 := by
  apply volume_transverseCoreHittingDomain hU
  · intro y hy
    exact A.map.contDiff.contDiffAt.comp y (hC y hy)
  · exact fun y hy => (A.positive (C y)).mpr (hp y hy)
  · exact fun y hy => (A.constraint (C y)).trans (hc y hy)
  · intro y hy
    have hd := (A.map.hasFDerivAt.comp y ((hC y hy).differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    change normalizedSectionFlux (A.map (C y))
      (fun i => A.map (fderiv ℝ C y (Pi.single i 1))) ≠ 0
    rw [A.sectionFlux]
    exact hflux y hy
  · exact hZ

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.EraCurve.constant_admissible {B : ℝ} (hB : 0 < B) : (constant B).Admissible B := by
  intro r _
  refine ⟨half_pos hB, half_pos hB, by dsimp [constant]; linarith,
    contDiffAt_const, contDiffAt_const, ?_, ?_⟩ <;>
    simpa only [constant, deriv_const, abs_zero] using Real.sqrt_nonneg (B / 2)

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

@[simp] private theorem BianchiIX.EraCurve.family_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) :
    Γ.family η J σ B [] = Γ := by simp [family, List.reverseRecOn]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

@[simp] private theorem BianchiIX.EraCurve.family_append (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) (a : ℕ+) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).nextCurve η J σ (eraAmplitude B w.length) a := by
  simp [family, List.reverseRecOn]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.EraCurve.family_append_of_retained (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ)
    (w : List ℕ+) (a : ℕ+) (ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).successor η J a.natPred ((eraAmplitude B w.length) ^ σ) := by
  rw [family_append, nextCurve, if_pos ha]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.EraCurve.family_admissible {η σ B Bstar C : ℝ} {J : ℕ} {Γ : EraCurve}
    (hB : B ∈ Ioc 0 Bstar) (hBs : Bstar ≤ 1) (hΓ : Γ.Admissible B)
    (H : ∀ b ∈ Ioc 0 Bstar, ∀ γ : EraCurve, γ.Admissible b → γ.StepEstimates η J σ b C)
    (w : List ℕ+) : (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) := by
  have hb (n : ℕ) : eraAmplitude B n ∈ Ioc 0 Bstar :=
    ⟨eraAmplitude_pos hB.1 n, (eraAmplitude_le hB.1.le (hB.2.trans hBs) n).trans hB.2⟩
  induction w using List.reverseRecOn with
  | nil => simpa using hΓ
  | append_singleton w a ih =>
    rw [family_append, List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    unfold nextCurve
    split_ifs with ha
    · exact (H _ (hb w.length) _ ih).successor_admissible a.natPred ha
    · exact constant_admissible (Real.rpow_pos_of_pos (hb w.length).1 _)

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.exists_era_curve_family :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B → ∀ w : List ℕ+,
            (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
            (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_curve_step
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bs, hBs, hBsone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨C, hC, Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ w
  have ha := EraCurve.family_admissible hB hBsone.le hΓ H w
  exact ⟨ha, H _ ⟨eraAmplitude_pos hB.1 _,
    (eraAmplitude_le hB.1.le (hB.2.trans hBsone.le) _).trans hB.2⟩ _ ha⟩

end
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
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.inverseTree_estimates {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    (Γ.inverseTree η J σ B C H).BranchEstimates (fun n => C * eraAmplitude B n)
      (fun n => 5 * C * Real.sqrt (eraAmplitude B n)) := by
  refine ⟨Subset.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro w a y hy
    obtain ⟨_, hy⟩ := mem_eraTreeDomain.mp hy
    exact ⟨by linarith [(H w).beta_pos, hy.1], by linarith [(H w).beta_pos, hy.2]⟩
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.1.differentiableAt (by norm_num)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.1.ne
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hv := (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.1
    have hden : 1 ≤ ((a.natPred : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) a.natPred]
    have hb : 0 ≤ C * eraAmplitude B w.length := mul_nonneg hC (eraAmplitude_pos hB _).le
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using hv.trans (div_le_self hb hden)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.inverseTree_successor_match {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (w : List ℕ+) (a : ℕ+) (y : ℝ)
    (hy : y ∈ (Γ.inverseTree η J σ B C H).domain w a) :
    let x := 2 / (Γ.inverseTree η J σ B C H).branch w a y
    let X := (Γ.family η J σ B w).state x
    eraOutputRadius η J a.natPred X = 2 / y ∧
      (Γ.family η J σ B (w ++ [a])).U (2 / y) = eraOutputState η J a.natPred X 1 ∧
      (Γ.family η J σ B (w ++ [a])).W (2 / y) = eraOutputState η J a.natPred X 3 := by
  obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
  have hm := (H w).successor_match a.natPred ha y ⟨hy.1.le, hy.2.le⟩
  dsimp only
  rw [family_append_of_retained Γ η J σ B w a ha]
  exact hm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_era_selected_return :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          (∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
            Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B →
            ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ x : ℝ,
              (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bstar m ↔
                x ∈ eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := by
  obtain ⟨δm, hδm, hδmax, HM⟩ := exists_era_selected_inputs_measurable
  obtain ⟨δi, hδi, _, HI⟩ := exists_era_selected_inputs_inverse
  refine ⟨min δm δi, lt_min hδm hδi, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bm, hBm, hBmone, Hm⟩ := HM η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bi, hBi, _, Hi⟩ := HI η hη (hηδ.trans (min_le_right _ _)) J (by omega) σ hσ hσone hσJ
  refine ⟨min Bm Bi, lt_min hBm hBi, (min_le_left _ _).trans_lt hBmone, ?_, ?_⟩
  · intro m
    apply eraSelectedInputs_measurable_of_contDiff hσ.le
    intro p hp
    exact (Hm m).1 p ⟨⟨hp.1.1, hp.1.2.trans (min_le_left _ _)⟩, hp.2⟩
  · intro B hB Γ hΓ m hm x
    have hBi' : B ∈ Ioc 0 Bi := ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
    have heq : (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ (min Bm Bi) m ↔
        (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bi m := by
      simp only [eraSelectedInputs, eraInputSelection, mem_ofPred_eq, hB, hBi', true_and]
    exact heq.trans (Hi B hBi' Γ hΓ m hm x)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixState_append (η : ℝ) (J : ℕ) (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    eraPrefixState η J (v ++ w) p = eraPrefixState η J w (eraPrefixState η J v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih => exact ih _

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

private theorem BianchiIX.eraPrefixState_budget (η : ℝ) (J : ℕ) (w : List ℕ+) (p : ℝ × CoreAngleState)
    (hp : 0 ≤ p.1) : (eraPrefixState η J w p).1 = eraAmplitude p.1 w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [eraPrefixState_append]
    change (eraPrefixState η J w p).1 ^ (4 / 3 : ℝ) = _
    rw [ih, List.length_append, List.length_singleton, eraAmplitude_succ hp]

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

private theorem BianchiIX.eraSurvivorDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (eraSurvivorDomain η J σ Bstar) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w => (eraPrefixDomain_measurable H w.val).1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_compactEra_digit {N : ℕ} {γ β : ℝ} {X : CoreAngleState}
    (hγ : 0 < γ) (hβ : 0 < β) (hβγ : β < γ / 4) (hβN : β < 1 / ((N : ℝ) + 2))
    (hX : X ∈ compactEraPhase N γ) :
    ∃ m : ℕ, m + 1 = ⌊X 0 / 2⌋₊ ∧ m + 1 ≤ N ∧ m < ⌊1 / β⌋₊ ∧
      X 0 ∈ Icc (2 * ((m : ℝ) + 1 + β)) (2 * ((m : ℝ) + 2 - β)) ∧
      X 0 / 2 - ((m : ℝ) + 1) ∈ Icc γ (1 - γ) := by
  let n := ⌊X 0 / 2⌋₊
  have hn1 : 1 ≤ n := (Nat.one_le_floor_iff _).mpr (by linarith only [hX.1, hγ])
  have hnN : n ≤ N := Nat.floor_le_of_le (by linarith only [hX.2.1])
  have hnreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn1
  have hNrec : (N : ℝ) ≤ 1 / β := by
    have H := (lt_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 2)).mp hβN
    apply (le_div_iff₀ hβ).mpr
    nlinarith only [H, hβ]
  have hcut : N ≤ ⌊1 / β⌋₊ := Nat.le_floor hNrec
  have hfrac : X 0 / 2 - (((n - 1 : ℕ) : ℝ) + 1) ∈ Icc γ (1 - γ) := by
    rw [hnreal]
    exact hX.2.2
  refine ⟨n - 1, by omega, by omega, by omega, ?_, hfrac⟩
  constructor <;> linarith only [hfrac.1, hfrac.2, hβγ, hγ]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.compactEra_retained_margin {γ β f y : ℝ}
    (hβγ : β < γ / 4) (hf : f ∈ Icc γ (1 - γ))
    (herror : |y - f| < β / 4) :
    7 * γ / 16 < y - 2 * β ∧ 7 * γ / 16 < (1 - 2 * β) - y ∧
      y ∈ Ioo (2 * β) (1 - 2 * β) := by
  obtain ⟨hl, hu⟩ := abs_lt.mp herror
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hl, hu, hf.1, hf.2, hβγ]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_compactEra_step :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 → ∀ Bcap : ℝ, 0 < Bcap →
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ Bstar < 1 ∧
            ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
              X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
                ∃ m : ℕ, m + 1 = ⌊X 0 / 2⌋₊ ∧ m + 1 ≤ N ∧
                  (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
                  0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
                  eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ) ∧
                  ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ N γ hγ _ Bcap hcap
  obtain ⟨C, _, Bi, hBi, hBione, Hi⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bb, hBb, _, Hb⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => 1) (p := fun _ => σ) (ε := fun _ => min (γ / 4) (1 / ((N : ℝ) + 2)))
    (by intros; norm_num) (by intros; exact hσ)
    (by intros; exact lt_min (by positivity) (by positivity)) (by norm_num : (0 : ℝ) < 1)
  refine ⟨min Bi (min Bcap Bb), lt_min hBi (lt_min hcap hBb),
    (min_le_right _ _).trans (min_le_left _ _), (min_le_left _ _).trans_lt hBione, ?_⟩
  intro B hB X hX hu hw hsum
  have hBi' : B ∈ Ioc 0 Bi := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBcap : B ∈ Ioc 0 Bcap := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hβ : 0 < B ^ σ := Real.rpow_pos_of_pos hB.1 _
  have hβsmall : B ^ σ < min (γ / 4) (1 / ((N : ℝ) + 2)) := by
    simpa only [one_mul] using Hb B ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
      0 (Finset.mem_univ _)
  obtain ⟨m, hcount, hN, hm, hr, hf⟩ := exists_compactEra_digit hγ hβ
    (hβsmall.trans_le (min_le_left _ _)) (hβsmall.trans_le (min_le_right _ _)) hX
  obtain ⟨Herr, Hmargin, hU, hW, Hsum, Hvalid⟩ := Hi m (B, X) ⟨hBi', hm, hu, hw, hsum, hr⟩
  have Hret := compactEra_retained_margin (hβsmall.trans_le (min_le_left _ _)) hf
    (Herr.trans_lt Hmargin)
  exact ⟨m, hcount, hN, ⟨⟨hBcap, hm, hu, hw, hsum, hr⟩, Hret.2.2⟩, hU, hW, Hsum, Hvalid⟩

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
open BianchiIX.EraCurve

@[simp] private theorem BianchiIX.EraCurve.treeState_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B x : ℝ) :
    Γ.treeState η J σ B [] x = (B, Γ.state (2 / x)) := by simp [treeState]

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve

private theorem BianchiIX.EraCurve.realization_of_estimates {Γ : EraCurve} {η σ B Bcap C : ℝ} {J : ℕ}
    (hB : B ∈ Ioc 0 Bcap) (hcap : Bcap ≤ 1)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
      (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (Hselect : ∀ b ∈ Ioc 0 Bcap, ∀ γ : EraCurve, γ.Admissible b →
      ∀ m : ℕ, m < ⌊1 / b ^ σ⌋₊ → ∀ x : ℝ,
        (b, γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bcap m ↔
          x ∈ eraInverseBranch η J m (b ^ σ) γ.U γ.W '' Ioo (2 * b ^ σ) (1 - 2 * b ^ σ)) :
    Γ.Realization η J σ B Bcap (Γ.inverseTree η J σ B C (fun w => (H w).2)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w a y hy
    have hm := inverseTree_successor_match (fun w => (H w).2) w a y hy
    apply Prod.ext
    · change (eraAmplitude B w.length) ^ (4 / 3 : ℝ) = eraAmplitude B (w ++ [a]).length
      rw [List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    · funext i
      fin_cases i
      · exact hm.1
      · exact hm.2.1.symm
      · exact hm.2.2.symm
  · intro w a x
    have hb : eraAmplitude B w.length ∈ Ioc 0 Bcap :=
      ⟨eraAmplitude_pos hB.1 _, (eraAmplitude_le hB.1.le (hB.2.trans hcap) _).trans hB.2⟩
    by_cases ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
    · change (eraAmplitude B w.length, (Γ.family η J σ B w).state (2 / x)) ∈ _ ↔
        x ∈ Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a
      rw [eraTreeDomain, if_pos ha]
      exact Hselect _ hb _ (H w).1 a.natPred ha x
    · have hd : (Γ.inverseTree η J σ B C (fun w => (H w).2)).domain w a = ∅ := by
        change eraTreeDomain σ B w a = ∅
        rw [eraTreeDomain, if_neg ha]
      rw [hd, image_empty, mem_empty_iff_false, iff_false]
      exact fun hx => ha hx.1.2.1

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.prefix_state (w : List ℕ+) (y : ℝ) (hy : y ∈ T.terminal w) :
    eraPrefixState η J w (B, Γ.state (2 / T.toRoot w y)) = Γ.treeState η J σ B w y := by
  induction w using List.reverseRecOn generalizing y with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [T.terminal_append] at hy
    rw [eraPrefixState_append, T.toRoot_append]
    change eraBudgetReturn η J a.natPred
      (eraPrefixState η J w (B, Γ.state (2 / T.toRoot w (T.branch w a y)))) = _
    rw [ih _ hy.2]
    exact R.step w a y hy.1

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.prefix_domain_iff_cell (w : List ℕ+) (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraPrefixDomain η J σ Bcap w ↔ x ∈ T.cell w := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixDomain, hx]
  | append_singleton w a ih =>
    rw [mem_eraPrefixDomain_append, T.cell_append]
    simp only [eraPrefixDomain, mem_inter_iff, mem_preimage, mem_univ, and_true]
    constructor
    · rintro ⟨hp, hnext⟩
      obtain ⟨z, hz, hzx⟩ := ih.mp hp
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs] at hnext
      exact ⟨z, ⟨hz, (R.selected w a z).mp hnext⟩, hzx⟩
    · rintro ⟨z, ⟨hz, hnext⟩, hzx⟩
      refine ⟨ih.mpr ⟨z, hz, hzx⟩, ?_⟩
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs]
      exact (R.selected w a z).mpr hnext

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.survivor_iff (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraSurvivorDomain η J σ Bcap ↔ x ∈ T.survivors := by
  constructor
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
    exact T.mem_level.mpr ⟨w.val, w.property, (R.prefix_domain_iff_cell w.val x hx).mp hw⟩
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw, hc⟩ := T.mem_level.mp (mem_iInter.mp hp n)
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, (R.prefix_domain_iff_cell w x hx).mpr hc⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.word_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) (n : ℕ) : EraSurvivor.word p n = T.word x n := by
  apply (EraSurvivor.word_eq_iff p (T.word_length x n)).mpr
  rw [hp]
  exact (R.prefix_domain_iff_cell _ _ (T.survivors_subset_root x.property)).mpr (T.mem_word_cell x n)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.digits_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.digits p = T.digits x := by
  funext n
  have heq := (EraSurvivor.word_succ p n).symm.trans
    ((R.word_eq_tree x p hp (n + 1)).trans (T.word_succ x n))
  rw [R.word_eq_tree x p hp n] at heq
  exact List.singleton_inj.mp (List.append_inj_right heq rfl)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_normalizedWallProductsBound {x : NormalizedState}
    (H : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ᶠ t in atTop, normalizedWallProductsBound Δ (normalizedMaxCurve x 0 t) := by
  have hcut : 0 < Δ ^ 2 / 4 := by positivity
  filter_upwards [(H 0 1 (by decide)).eventually (gt_mem_nhds hcut),
    (H 1 2 (by decide)).eventually (gt_mem_nhds hcut),
    (H 2 0 (by decide)).eventually (gt_mem_nhds hcut)] with t h01 h12 h20
  change normalizedMaxCurve x 0 t 2 * normalizedMaxCurve x 0 t 3 < Δ ^ 2 / 4 at h01
  change normalizedMaxCurve x 0 t 3 * normalizedMaxCurve x 0 t 4 < Δ ^ 2 / 4 at h12
  change normalizedMaxCurve x 0 t 4 * normalizedMaxCurve x 0 t 2 < Δ ^ 2 / 4 at h20
  exact ⟨by nlinarith only [h01], by nlinarith only [h12], by nlinarith only [h20]⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraSurvivor
open EraCurve.Realization

private theorem BianchiIX.EraSurvivor.boundedDigitDomain_measurable {η σ Bcap : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (boundedDigitDomain η J σ Bcap) := by
  apply (eraSurvivorDomain_measurable H).subtype_image
  simp only [ofPred_exists, ofPred_forall]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
    measurableSet_le (measurable_subtype_coe.comp ((measurable_pi_apply n).comp (digits_measurable H))) measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraSurvivor
open EraCurve.Realization

private theorem BianchiIX.EraCurve.Realization.volume_curveBoundedDigits_zero {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ}
    {T : InverseBranchTree} (R : Γ.Realization η J σ B Bcap T)
    {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [E.typicalSurvivors_ae_eq hBirkhoff hbudget] with x hx
  rintro ⟨hxunit, p, hp, hpx⟩
  change p.val = (B, Γ.state (2 / x)) at hpx
  have hxroot : x ∈ T.root := by rwa [R.root]
  have hps : (B, Γ.state (2 / x)) ∈ eraSurvivorDomain η J σ Bcap := by
    rw [← hpx]
    exact p.property
  let xt : T.survivors := ⟨x, (R.survivor_iff x hxroot).mp hps⟩
  have htyp : x ∈ T.typicalSurvivors := by
    change T.typicalSurvivors x
    rw [hx]
    exact xt.property
  have ht := (T.mem_typicalSurvivors xt).mp htyp
  have hdigits := R.digits_eq_tree xt p hpx
  change ∃ N : ℕ, ∀ n, (EraSurvivor.digits p n : ℕ) ≤ N at hp
  exact not_bounded_digits_of_typical ht (by simpa only [hdigits] using hp)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraSurvivor
open EraCurve.Realization

private theorem BianchiIX.exists_era_curve_boundedDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap) ∧
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
            ∀ Γ : EraCurve, Γ.Admissible B →
              volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0 := by
  obtain ⟨δt, hδt, hδmax, HT⟩ := exists_era_curve_family
  obtain ⟨δs, hδs, _, HS⟩ := exists_era_selected_return
  refine ⟨min δt δs, lt_min hδt hδs, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bt, hBt, _, Htree⟩ := HT η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bs, hBs, hBsone, Hmeas, Hselect⟩ := HS η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hCi : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC0
  obtain ⟨Bb, hBb, _, Hbudget⟩ := exists_era_budget_threshold hσ hC0 hCi (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨Bs, hBs, hBsone, EraSurvivor.boundedDigitDomain_measurable Hmeas,
    min Bt (min Bs Bb), lt_min hBt (lt_min hBs hBb), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro B hB Γ hΓ
  have hBt' : B ∈ Ioc 0 Bt := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBs' : B ∈ Ioc 0 Bs := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hnodes := Htree B hBt' Γ hΓ
  let T := Γ.inverseTree η J σ B C (fun w => (Hnodes w).2)
  have R : Γ.Realization η J σ B Bs T := EraCurve.realization_of_estimates hBs' hBsone.le Hnodes Hselect
  have E := EraCurve.inverseTree_estimates hB.1 hC0 (fun w => (Hnodes w).2)
  obtain ⟨hsmall, _, _⟩ := Hbudget B hBb'
  have hJreal : (2 : ℝ) ≤ (2 * J : ℕ) := by exact_mod_cast (show 2 ≤ 2 * J by omega)
  have hσhalf : σ ≤ 1 / 2 := by nlinarith only [hσJ, hJreal, hσ]
  exact R.volume_curveBoundedDigits_zero E hBirkhoff
    (era_distortion_budget hB.1 (hBs'.2.trans hBsone.le) hσ.le hσhalf hsmall hC0 hCi).2.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_coreBoundedDigits {η σ B Bcap : ℝ} {J : ℕ}
    (H : MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap)) :
    MeasurableSet (coreBoundedDigits η J σ B Bcap) := by
  have hs : Measurable (fun q : CoreAngleState => q 1 + q 2) := by fun_prop
  have hp : Measurable (fun q : CoreAngleState => (B, ![2 / q 0, q 1, q 2])) := by fun_prop
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 0)).inter
    ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 2)).inter
        ((measurableSet_le hs measurable_const).inter (H.preimage hp))))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_coreBoundedDigits_zero {η σ B Bcap : ℝ} {J : ℕ}
    (hjoint : MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap))
    (H : ∀ Γ : EraCurve, Γ.Admissible B →
      volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0) :
    volume (coreBoundedDigits η J σ B Bcap) = 0 := by
  let A := coreBoundedDigits η J σ B Bcap
  have hA : MeasurableSet A := measurableSet_coreBoundedDigits hjoint
  have hslices (u w : ℝ) : volume ((fun x : ℝ => ![x, u, w]) ⁻¹' A) = 0 := by
    by_cases hl : 0 < u ∧ 0 < w ∧ u + w ≤ B
    · let Γ : EraCurve := ⟨fun _ => u, fun _ => w⟩
      have hΓ : Γ.Admissible B := by
        intro r _
        refine ⟨hl.1, hl.2.1, hl.2.2, contDiffAt_const, contDiffAt_const, ?_, ?_⟩ <;>
          simpa only [Γ, deriv_const, abs_zero] using Real.sqrt_nonneg _
      have heq : (fun x : ℝ => ![x, u, w]) ⁻¹' A =
          EraSurvivor.curveBoundedDigits Γ η J σ B Bcap := by
        ext x
        simp [A, coreBoundedDigits, EraSurvivor.curveBoundedDigits, EraCurve.state, Γ, hl.1, hl.2.1, hl.2.2]
      rw [heq]
      exact H Γ hΓ
    · have heq : (fun x : ℝ => ![x, u, w]) ⁻¹' A = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hl ⟨hx.2.1, hx.2.2.1, hx.2.2.2.1⟩
      rw [heq, measure_empty]
  change volume A = 0
  have hind : Measurable (A.indicator (1 : CoreAngleState → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_indicator_one hA, lintegral_three_coordinates hind]
  have hinner (u w : ℝ) : (∫⁻ x : ℝ, A.indicator (1 : CoreAngleState → ℝ≥0∞) ![x, u, w]) = 0 := by
    have heq : (fun x : ℝ => A.indicator (1 : CoreAngleState → ℝ≥0∞) ![x, u, w]) =
        ((fun x : ℝ => ![x, u, w]) ⁻¹' A).indicator 1 := by
      funext x
      rfl
    rw [heq, lintegral_indicator_one (hA.preimage (by fun_prop)), hslices]
  simp_rw [hinner]
  simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.compactEraHistories_finite_prefix {η σ Bcap Bstar γ : ℝ} {J N : ℕ}
    (hBstar : Bstar ≤ 1)
    (Hstep : ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
      X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
        ∃ m : ℕ, (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
          0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
          eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ))
    {p : ℝ × CoreAngleState} (hp : p.1 ∈ Ioc 0 Bstar)
    (hu : 0 < p.2 1) (hw : 0 < p.2 2) (hsum : p.2 1 + p.2 2 ≤ p.1)
    (Hcompact : compactEraHistories η J σ Bcap N γ p) (n : ℕ) :
    ∃ w : List ℕ+, w.length = n ∧ p ∈ eraPrefixDomain η J σ Bcap w ∧
      let q := eraPrefixState η J w p
      0 < q.2 1 ∧ 0 < q.2 2 ∧ q.2 1 + q.2 2 ≤ q.1 := by
  induction n with
  | zero => exact ⟨[], rfl, mem_univ _, hu, hw, hsum⟩
  | succ n ih =>
    obtain ⟨w, hlen, hmem, hU, hW, Hsum⟩ := ih
    let q := eraPrefixState η J w p
    have hq : q.1 ∈ Ioc 0 Bstar := by
      rw [show q.1 = eraAmplitude p.1 w.length from eraPrefixState_budget η J w p hp.1.le]
      exact ⟨eraAmplitude_pos hp.1 _, (eraAmplitude_le hp.1.le (hp.2.trans hBstar) _).trans hp.2⟩
    obtain ⟨m, hselected, hU', hW', Hsum'⟩ := Hstep q.1 hq q.2 (Hcompact w hmem) hU hW Hsum
    let a : ℕ+ := ⟨m + 1, by omega⟩
    have ha : a.natPred = m := by simp [a, PNat.natPred]
    have hnext : p ∈ eraPrefixDomain η J σ Bcap (w ++ [a]) := by
      apply (mem_eraPrefixDomain_append η J σ Bcap w [a] p).mpr
      refine ⟨hmem, ?_⟩
      simpa only [eraPrefixDomain, ha, mem_inter_iff, mem_preimage, mem_univ, and_true] using hselected
    have hstate : eraPrefixState η J (w ++ [a]) p = eraBudgetReturn η J m q := by
      rw [eraPrefixState_append]
      simp only [eraPrefixState, ha, Function.comp_apply, id_eq, q]
    refine ⟨w ++ [a], by simp only [List.length_append, List.length_singleton, hlen], hnext, ?_⟩
    rw [hstate]
    exact ⟨hU', hW', Hsum'⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.compactEraHistories_survives {η σ Bcap Bstar γ : ℝ} {J N : ℕ}
    (hBstar : Bstar ≤ 1)
    (Hstep : ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
      X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
        ∃ m : ℕ, (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
          0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
          eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ))
    {p : ℝ × CoreAngleState} (hp : p.1 ∈ Ioc 0 Bstar)
    (hu : 0 < p.2 1) (hw : 0 < p.2 2) (hsum : p.2 1 + p.2 2 ≤ p.1)
    (Hcompact : compactEraHistories η J σ Bcap N γ p) : p ∈ eraSurvivorDomain η J σ Bcap := by
  apply mem_iInter.mpr
  intro n
  obtain ⟨w, hlen, hmem, _⟩ := compactEraHistories_finite_prefix hBstar Hstep hp hu hw hsum Hcompact n
  exact mem_iUnion.mpr ⟨⟨w, hlen⟩, hmem⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EraSurvivor.digits_le_of_compactHistories {η σ Bcap γ : ℝ} {J N : ℕ}
    (p : eraSurvivorDomain η J σ Bcap)
    (Hcompact : compactEraHistories η J σ Bcap N γ p.val) (n : ℕ) : (digits p n : ℕ) ≤ N := by
  have Hnext := mem_word_domain p (n + 1)
  rw [word_succ] at Hnext
  have hs := ((mem_eraPrefixDomain_append η J σ Bcap (word p n) [digits p n] p.val).mp Hnext).2.1
  have hphase := (Hcompact (word p n) (mem_word_domain p n)).2.1
  have hβ : 0 < (eraPrefixState η J (word p n) p.val).1 ^ σ := Real.rpow_pos_of_pos hs.1.1.1 _
  have hlow := hs.1.2.2.2.2.2.1
  have hcast : ((digits p n).natPred : ℝ) + 1 = (digits p n : ℝ) := by
    exact_mod_cast (digits p n).natPred_add_one
  rw [hcast] at hlow
  exact_mod_cast (show (digits p n : ℝ) ≤ (N : ℝ) by linarith only [hlow, hphase, hβ])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_compactEra_survival :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 → ∀ Bcap : ℝ, 0 < Bcap →
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ Bstar < 1 ∧
            ∀ p : ℝ × CoreAngleState, p.1 ∈ Ioc 0 Bstar →
              0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
              compactEraHistories η J σ Bcap N γ p → p ∈ EraSurvivor.boundedDigitDomain η J σ Bcap := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_compactEra_step
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ N γ hγ hγmax Bcap hcap
  obtain ⟨Bstar, hBstar, hBcap, hBone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ N γ hγ hγmax Bcap hcap
  refine ⟨Bstar, hBstar, hBcap, hBone, ?_⟩
  intro p hp hu hw hsum Hcompact
  have hs : p ∈ eraSurvivorDomain η J σ Bcap := compactEraHistories_survives hBone.le (by
    intro B hB X hX hU hW Hsum
    obtain ⟨m, _, _, Hsel, hU', hW', Hsum', _⟩ := H B hB X hX hU hW Hsum
    exact ⟨m, Hsel, hU', hW', Hsum'⟩) hp hu hw hsum Hcompact
  let q : eraSurvivorDomain η J σ Bcap := ⟨p, hs⟩
  exact ⟨q, ⟨N, EraSurvivor.digits_le_of_compactHistories q Hcompact⟩, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.curveCompactEraHistories_subset_boundedDigits {η σ B Bcap γ : ℝ} {J N : ℕ} {Γ : EraCurve}
    (hΓ : Γ.Admissible B)
    (H : ∀ X : CoreAngleState, 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap) :
    curveCompactEraHistories Γ η J σ B Bcap N γ ⊆ EraSurvivor.curveBoundedDigits Γ η J σ B Bcap := by
  intro x hx
  have hr : 2 < 2 / x := (lt_div_iff₀ hx.1.1).mpr (by linarith only [hx.1.2])
  obtain ⟨hu, hw, hsum, _⟩ := hΓ (2 / x) hr
  exact ⟨hx.1, H _ hu hw hsum hx.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreCompactEraHistories_subset_boundedDigits {η σ B Bcap γ : ℝ} {J N : ℕ}
    (H : ∀ X : CoreAngleState, 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap) :
    coreCompactEraHistories η J σ B Bcap N γ ⊆ coreBoundedDigits η J σ B Bcap := by
  intro q hq
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
    H _ hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_compactEra_null (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
            ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
              (∀ Γ : EraCurve, Γ.Admissible B →
                volume (curveCompactEraHistories Γ η J σ B Bcap N γ) = 0) ∧
              volume (coreCompactEraHistories η J σ B Bcap N γ) = 0 := by
  obtain ⟨δs, hδs, hδmax, HS⟩ := exists_compactEra_survival
  obtain ⟨δb, hδb, _, HB⟩ := exists_era_curve_boundedDigits_zero hBirkhoff
  refine ⟨min δs δb, lt_min hδs hδb, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hjoint, Bb, hBb, hBbcap, Hb⟩ :=
    HB η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro N γ hγ hγmax
  obtain ⟨Bs, hBs, _, _, Hs⟩ := HS η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
    N γ hγ hγmax Bcap hcap
  refine ⟨min Bs Bb, lt_min hBs hBb, (min_le_right _ _).trans hBbcap, ?_⟩
  intro B hB
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  have H (X : CoreAngleState) : 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap :=
    Hs (B, X) ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  refine ⟨?_, measure_mono_null (coreCompactEraHistories_subset_boundedDigits H)
    (volume_coreBoundedDigits_zero hjoint (Hb B hBb'))⟩
  intro Γ hΓ
  exact measure_mono_null (curveCompactEraHistories_subset_boundedDigits hΓ H) (Hb B hBb' Γ hΓ)

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
open Set MeasureTheory

private theorem BianchiIX.exists_taubAvoidingCore_null (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Bstar > (0 : ℝ), ∀ B ∈ Ioc 0 Bstar,
      (∀ Γ : EraCurve, Γ.Admissible B → volume (curveTaubAvoidance Γ ε) = 0) ∧
      volume (coreTaubAvoidance ε B) = 0 := by
  obtain ⟨δh, hδh, _, HH⟩ := exists_compactEraHistories_of_taub_avoidance
  obtain ⟨δn, hδn, _, HN⟩ := exists_compactEra_null hBirkhoff
  let η := min δh δn / 2
  have hη : 0 < η := div_pos (lt_min hδh hδn) (by norm_num)
  have hηh : η ≤ δh := by dsimp [η]; linarith only [min_le_left δh δn, hδh]
  have hηn : η ≤ δn := by dsimp [η]; linarith only [min_le_right δh δn, hδn]
  obtain ⟨N, γ, hγ, hγmax, Bh, hBh, _, Hh⟩ :=
    HH η hη hηh 20 (by omega) (1 / 100) (by norm_num) (by norm_num) (by norm_num) ε hε
  obtain ⟨Bcap, _, _, Hn⟩ :=
    HN η hη hηn 20 (by omega) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bn, hBn, _, Hnull⟩ := Hn N γ hγ hγmax
  refine ⟨min Bh Bn, lt_min hBh hBn, ?_⟩
  intro B hB
  have hBh' : B ∈ Ioc 0 Bh := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  obtain ⟨Hcurve, Hcore⟩ := Hnull B ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  constructor
  · intro Γ hΓ
    apply measure_mono_null (t := curveCompactEraHistories Γ η 20 (1 / 100) B Bcap N γ) _ (Hcurve Γ hΓ)
    intro x hx
    have hr : 2 < 2 / x := (lt_div_iff₀ hx.1.1).mpr (by linarith only [hx.1.2])
    obtain ⟨hu, hw, hsum, _⟩ := hΓ (2 / x) hr
    exact ⟨hx.1, Hh Bcap (B, Γ.state (2 / x)) hBh'
      (by change 2 - γ / 2 ≤ 2 / x; linarith only [hr, hγ]) hu hw hsum hx.2⟩
  · apply measure_mono_null (t := coreCompactEraHistories η 20 (1 / 100) B Bcap N γ) _ Hcore
    intro q hq
    have hr : 2 < 2 / q 0 := (lt_div_iff₀ hq.1.1).mpr (by linarith only [hq.1.2])
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
      Hh Bcap (B, ![2 / q 0, q 1, q 2]) hBh'
        (by change 2 - γ / 2 ≤ 2 / q 0; linarith only [hr, hγ])
        hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exists_late_null_core_target (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B > (0 : ℝ), volume (coreTaubAvoidance ε B) = 0 ∧
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) →
        (∀ i j : Fin 3, i ≠ j → Tendsto
          (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0)) →
        ∀ r : ℝ, ∃ T > max r 0, ∃ a : Fin 6, ∃ q ∈ coreTaubAvoidance ε B,
          T ∈ normalizedMaxDomain x 0 ∧
          fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]) =
            (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
          0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))
            (normalizedField (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))) := by
  obtain ⟨B, hB, Hnull⟩ := exists_taubAvoidingCore_null hBirkhoff hε
  obtain ⟨N, γ, hγ, _, Hcore⟩ := exists_arbitrarily_late_compact_core hε
  refine ⟨B, hB, (Hnull B ⟨hB, le_rfl⟩).2, ?_⟩
  intro x hc hp ha hprod r
  obtain ⟨T, hT, a, Y, hdom, heq, hphase, hU, hW, hsum, havoid, htrans⟩ :=
    Hcore B hB x hc hp ha (fun _ hΔ => eventually_normalizedWallProductsBound hprod hΔ) r
  have hk : 2 < Y 0 := by linarith only [hphase.1, hγ]
  have hkpos : 0 < Y 0 := by linarith only [hk]
  let q : CoreAngleState := ![2 / Y 0, Y 1, Y 2]
  have hrec : (![2 / q 0, q 1, q 2] : CoreAngleState) = Y := by
    ext i
    fin_cases i
    · change 2 / (2 / Y 0) = Y 0
      field_simp
    · rfl
    · rfl
  have hq : q ∈ coreTaubAvoidance ε B := by
    refine ⟨⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr hk⟩, hU, hW, hsum, ?_⟩
    rw [hrec]
    exact havoid
  refine ⟨T, hT, a, q, hq, hdom, ?_, ?_⟩
  · rwa [hrec]
  · rwa [hrec]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.contDiffAt_corePhaseSectionCoordinates (n : WithTop ℕ∞) {q : SectionCoordinates}
    (hq : q 0 ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ n corePhaseSectionCoordinates q := by
  have hk : 1 < 2 / q 0 := (lt_div_iff₀ hq.1).mpr (by linarith only [hq.2])
  have hcoord : ContDiffAt ℝ n (fun z : SectionCoordinates => (![2 / z 0, z 1, z 2] : CoreAngleState)) q := by
    have hne := hq.1.ne'
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (contDiff_coreSectionCoordinates n).contDiffAt.comp q
    ((contDiffAt_coreRadiusEntry n hk).comp q hcoord)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.volume_eventually_taub_avoiding_section
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {ε : ℝ} (hε : 0 < ε)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧
      (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))} = 0 := by
  obtain ⟨B, _, hnull, Hhit⟩ := exists_late_null_core_target hBirkhoff hε
  let Z := corePhaseSectionCoordinates '' coreTaubAvoidance ε B
  have hZ : volume Z = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun q hq => ((contDiffAt_corePhaseSectionCoordinates 1 hq.1).differentiableAt
        (by norm_num)).differentiableWithinAt) hnull
  have haxis (a : Fin 6) : volume
      (U ∩ transverseCoreHittingDomain (fun y => (axisFrame a).map (C y)) 0 Z) = 0 :=
    volume_axis_transverseCoreHittingDomain (axisFrame a) hU hC hp hc hflux hZ
  apply measure_mono_null (t := ⋃ a : Fin 6,
    U ∩ transverseCoreHittingDomain (fun y => (axisFrame a).map (C y)) 0 Z) _
      (measure_iUnion_null haxis)
  intro y hy
  obtain ⟨T, hT, a, q, hq, hdom, heq, htrans⟩ := Hhit (C y) (hc y hy.1) (hp y hy.1) hy.2.1 hy.2.2 0
  let z := coreRadiusEntry ![2 / q 0, q 1, q 2]
  have hposit : positiveWalls (fromProjectiveState z) := by
    rw [heq]
    exact ((axisFrame a).positive _).mpr
      (normalizedMaxCurve_forward (hp y hy.1) (hc y hy.1) (by simpa using hT.le)).2.1
  have hD : projectiveStateDenom z ≠ 0 := by
    intro hz
    simpa [fromProjectiveState, hz] using hposit.1
  have hflow : normalizedMaxCurve ((axisFrame a).map (C y)) 0 T = fromProjectiveState z :=
    ((axisFrame a).maxCurve hdom).trans heq.symm
  have hproj : toProjectiveState (normalizedMaxCurve ((axisFrame a).map (C y)) 0 T) = z := by
    rw [hflow, toProjectiveState_fromProjectiveState hD]
  refine mem_iUnion.mpr ⟨a, hy.1, T, ?_, ?_, ?_, ?_⟩
  · rwa [(axisFrame a).maxDomain]
  · change toProjectiveState _ 2 = 1
    rw [hproj]
    rfl
  · unfold normalizedEventRate
    rw [hflow]
    exact htrans.ne'
  · change coreSectionCoordinates (toProjectiveState _) ∈ Z
    rw [hproj]
    exact mem_image_of_mem corePhaseSectionCoordinates hq

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.volume_eventually_taub_separated_section
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧
      (∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i,
        ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))} = 0 := by
  let E (n : ℕ) := {y | y ∈ U ∧
    (∀ᶠ t in atTop, ∀ i, 1 / (n + 1 : ℝ) ≤
      normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
    (∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
        atTop (𝓝 0))}
  have hE (n : ℕ) : volume (E n) = 0 :=
    volume_eventually_taub_avoiding_section hBirkhoff (by positivity) hU hC hp hc hflux
  apply measure_mono_null (t := ⋃ n, E n) _ (measure_iUnion_null hE)
  rintro y ⟨hy, ⟨ε, hε, ha⟩, hd⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine mem_iUnion.mpr ⟨n, hy, ?_, hd⟩
  exact ha.mono fun t ht i => hn.le.trans (ht i)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.ae_arbitrarily_late_taub_approach
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0)) →
      ∀ ε > (0 : ℝ), ∀ r : ℝ, ∃ t ≥ r, ∃ i : Fin 3,
        normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i) < ε := by
  classical
  have hnull := withDensity_absolutelyContinuous volume ρ
    (volume_eventually_taub_separated_section hBirkhoff hU hC hp hc hflux)
  have hae : ∀ᵐ y ∂(volume.withDensity ρ), ¬(y ∈ U ∧
      (∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i,
        ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with y hy hyU hd ε hε r
  by_contra! hn
  apply hy
  exact ⟨hyU, ⟨ε, hε, (eventually_ge_atTop r).mono fun t ht i => hn t ht i⟩, hd⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.ae_transverse_late_primaryAxis_crossing
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0)) →
      ∃ i : Fin 3, ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0,
        c ∈ normalizedMaxDomain (C y) 0 ∧ ∃ z ∈ mainWallChartDomain h,
          axisWallChart (primaryAxisFrame i) h z = normalizedMaxCurve (C y) 0 c ∧
          |z 0| < d ∧ Real.exp (-z 1) < d ∧ Real.exp (-z 2) < d ∧
          normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve (C y) 0 c)) < η := by
  filter_upwards [ae_arbitrarily_late_taub_approach hBirkhoff hU hC hp hc hflux ρ,
    ae_primaryAxis_taubRadiusSq_pos hC hflux ρ] with y hvisit hr hy hprod
  exact exists_arbitrarily_late_primaryAxis_crossing (hc y hy) (hp y hy) (hr hy)
    hh hhmax hd hdh hprod (hvisit hy hprod)

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

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.ae_primaryAxis_infiniteReturns_of_decay
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t) *
          wallValue j (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t))
            atTop (𝓝 0)) →
      z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E := by
  intro E
  rw [ae_axisFamilyMeasure_iff]
  intro a
  have hflux (y : SectionCoordinates) (hy : y ∈ mainWallChartDomain h) :
      normalizedSectionFlux (axisWallChart (primaryAxisFrame a) h y)
        (fun i => fderiv ℝ (axisWallChart (primaryAxisFrame a) h) y (Pi.single i 1)) ≠ 0 := by
    change normalizedSectionFlux (axisWallChart (primaryAxisFrame a) h y)
      (axisWallChartFrame (primaryAxisFrame a) h y) ≠ 0
    rw [axisWallChart_signed_flux (primaryAxisFrame a) hh hy]
    exact neg_ne_zero.mpr (mainWallChartDensity_pos hh hy).ne'
  have H := ae_transverse_late_primaryAxis_crossing hBirkhoff hh hhmax hd hdh
    (isOpen_mainWallChartDomain h) (fun y hy => contDiffAt_axisWallChart (primaryAxisFrame a) hy 1)
    (fun y _ => axisWallChart_positive (primaryAxisFrame a) hh y)
    (fun _ hy => axisWallChart_constraint (primaryAxisFrame a) hy) hflux
    1
  rw [withDensity_one] at H
  filter_upwards [(mainWallMeasure_absolutelyContinuous h).ae_le (ae_restrict_of_ae H)] with y hy hz hprod
  refine ⟨hz, infinite_of_not_bddAbove ?_⟩
  obtain ⟨i, hi⟩ := hy hz.2 hprod
  rw [not_bddAbove_iff]
  intro R
  obtain ⟨c, hcR, _, w, hw, hchart, hs, hb, hc, _⟩ := hi R 1 (by norm_num)
  refine ⟨c, ?_, (le_max_left R 0).trans_lt hcR⟩
  rw [axisFamily_returnTimes_eq_physical_hits (fun _ => hh) (fun _ _ hw => hw.2)]
  refine ⟨(le_max_right R 0).trans_lt hcR, hz.2, (i, w), ?_, hchart⟩
  exact ⟨⟨hs.le, max_le hb.le hc.le⟩, hw⟩

end
end


theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {F : Set (Fin 3 × SectionCoordinates)} (hF : MeasurableSet F)
    (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E →
      WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) z) →
        axisFamilyChart primaryAxisFrame (fun _ => h) z ∈
          globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) := by
  intro E
  have hh1 : h ≤ 1 / 8 := hhmax.trans (by norm_num)
  have hd1 : d ≤ 1 / 8 := hdh.le.trans (by linarith only [hh1])
  have hE : ∀ i, MeasurableSet (E i) := fun _ =>
    (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
        Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1, (le_max_left _ _).trans (hy.1.2.trans hdh.le),
      (le_max_right _ _).trans (hy.1.2.trans hdh.le)⟩
  filter_upwards [ae_smallAxis_success_hitting hh hh1 hE hsmall hF hfinite,
    ae_primaryAxis_infiniteReturns_of_decay hBirkhoff hh hhmax hd hdh] with z hcap hrec hz hprod
  exact hcap (hrec hz hprod)

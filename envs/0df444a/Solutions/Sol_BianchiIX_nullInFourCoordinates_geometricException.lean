-- Prove2me | solution 1 for BianchiIX.nullInFourCoordinates_geometricException
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:17:46.356885+00:00
-- url     : https://prove2.me/submissions/1d17621a-4cdb-45d9-a386-55c092fecad7

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
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
import Theorems.Thm_BianchiIX_Literature_BrehmIXAttractorInput_wallProductDecay
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_eraAmplitude_le
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Theorems.Thm_BianchiIX_eraAmplitude_zero
import Theorems.Thm_BianchiIX_era_distortion_budget
import Theorems.Thm_BianchiIX_exists_arbitrarily_late_compact_core
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_compactEraHistories_of_taub_avoidance
import Theorems.Thm_BianchiIX_exists_era_budget_threshold
import Theorems.Thm_BianchiIX_exists_era_curve_step
import Theorems.Thm_BianchiIX_exists_era_input_estimates
import Theorems.Thm_BianchiIX_exists_era_output_estimates
import Theorems.Thm_BianchiIX_exists_era_selected_inputs_inverse
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_rebase
import Theorems.Thm_BianchiIX_not_bounded_digits_of_typical
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
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
import Mathlib.MeasureTheory.Constructions.Pi
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
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
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.NullInFourCoordinates.mono {S T : Set NormalizedState}
    (H : NullInFourCoordinates T) (hST : S ⊆ T) : NullInFourCoordinates S :=
  fun P hP => measure_mono_null (image_mono hST) (H P hP)

end
end

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

private theorem BianchiIX.NullInFourCoordinates.union {S T : Set NormalizedState}
    (HS : NullInFourCoordinates S) (HT : NullInFourCoordinates T) :
    NullInFourCoordinates (S ∪ T) := by
  intro P hP
  rw [image_union]
  exact measure_union_null (HS P hP) (HT P hP)

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
open Set MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.volume_first_coordinate_zero : volume {p : FourCoordinates | p 0 = 0} = 0 := by
  have hn : volume (({0} : Set ℝ) ×ˢ (univ : Set (Fin 3 → ℝ))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have H := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).quasiMeasurePreserving.preimage_null hn
  have heq : {p : FourCoordinates | p 0 = 0} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0) ⁻¹'
        (({0} : Set ℝ) ×ˢ (univ : Set (Fin 3 → ℝ))) := by
    ext p
    simp [MeasurableEquiv.piFinSuccAbove]
  rw [heq]
  exact H

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

private theorem BianchiIX.NullInFourCoordinates.linear_image {S : Set NormalizedState}
    (H : NullInFourCoordinates S) (A : NormalizedState →L[ℝ] NormalizedState) :
    NullInFourCoordinates (A '' S) := by
  intro P hP
  rw [← image_comp]
  exact H (P ∘ A) (hP.comp A.differentiable)

private theorem BianchiIX.nullInFourCoordinates_taubSubspace :
    NullInFourCoordinates {x | normalizedTaubRadiusSq x = 0} := by
  intro P hP
  let C : FourCoordinates → NormalizedState := fun q => ![q 1, 0, q 2, q 3, q 3]
  have hC : Differentiable ℝ C := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> dsimp [C] <;> fun_prop
  have hn : volume ((P ∘ C) '' {q : FourCoordinates | q 0 = 0}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hP.comp hC).differentiableOn volume_first_coordinate_zero
  apply measure_mono_null _ hn
  rintro _ ⟨x, hx, rfl⟩
  have hs : x 1 = 0 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hx
    nlinarith only [hx, sq_nonneg (x 3 - x 4)]
  have hw : x 3 = x 4 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hx
    nlinarith only [hx, sq_nonneg (x 1)]
  refine ⟨![0, x 0, x 2, x 3], by simp, congrArg P ?_⟩
  ext i
  fin_cases i <;> simp [C, hs, hw]

private theorem BianchiIX.nullInFourCoordinates_taubSubspaces : NullInFourCoordinates taubSubspaces := by
  apply (NullInFourCoordinates.iUnion (fun i : Fin 3 =>
    nullInFourCoordinates_taubSubspace.linear_image (primaryAxisFrame i).map.symm.toContinuousLinearMap)).mono
  intro x hx
  obtain ⟨i, hi⟩ := hx
  exact mem_iUnion.mpr ⟨i, (primaryAxisFrame i).map x, hi,
    (primaryAxisFrame i).map.symm_apply_apply x⟩

private theorem BianchiIX.contDiffAt_corePhasePhysicalState {q : CoreAngleState}
    (hq : q 0 ∈ Ioo (0 : ℝ) 1)
    (hD : projectiveStateDenom (coreRadiusEntry ![2 / q 0, q 1, q 2]) ≠ 0) :
    ContDiffAt ℝ 1 corePhasePhysicalState q := by
  have hk : 1 < 2 / q 0 := (lt_div_iff₀ hq.1).mpr (by linarith only [hq.2])
  have hcoord : ContDiffAt ℝ 1 (fun z : CoreAngleState => (![2 / z 0, z 1, z 2] : CoreAngleState)) q := by
    have hne := hq.1.ne'
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (contDiffAt_fromProjectiveState 1 hD).comp q
    ((contDiffAt_coreRadiusEntry 1 hk).comp q hcoord)

private theorem BianchiIX.nullInFourCoordinates_fixed_taub_avoidance
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {ε : ℝ} (hε : 0 < ε) :
    NullInFourCoordinates {x | x ∈ physicalPhaseSpace ∧
      (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) ∧
      WallProductDecay x} := by
  obtain ⟨B, _, hnull, Hhit⟩ := exists_late_null_core_target hBirkhoff hε
  let Z := coreTaubAvoidance ε B ∩
    {q | projectiveStateDenom (coreRadiusEntry ![2 / q 0, q 1, q 2]) ≠ 0}
  let C : Fin 6 → CoreAngleState → NormalizedState := fun a q =>
    (axisFrame a).map.symm (corePhasePhysicalState q)
  have hC (a : Fin 6) : ∀ q ∈ Z, ContDiffAt ℝ 1 (C a) q := fun q hq =>
    (axisFrame a).map.symm.contDiff.contDiffAt.comp q
      (contDiffAt_corePhasePhysicalState hq.1.1 hq.2)
  have hn := NullInFourCoordinates.iUnion (fun a => nullInFourCoordinates_orbitSaturation
    (hC a) (measure_mono_null inter_subset_left hnull))
  apply hn.mono
  intro x hx
  obtain ⟨T, _, a, q, hq, hdom, heq, _⟩ := Hhit x hx.1.2 hx.1.1 hx.2.1 hx.2.2 0
  have hposit : positiveWalls (corePhasePhysicalState q) := by
    change positiveWalls (fromProjectiveState _)
    rw [heq]
    exact ((axisFrame a).positive _).mpr ((maximalNormalizedSolution x 0).physical hx.1.1 hx.1.2 hdom).1
  have hqZ : q ∈ Z := by
    refine ⟨hq, ?_⟩
    intro hz
    simpa [corePhasePhysicalState, fromProjectiveState, hz] using hposit.1
  have hentry : C a q = normalizedMaxCurve x 0 T := by
    dsimp [C, corePhasePhysicalState]
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  have hinv := normalizedMaxCurve_inverse hdom
  rw [← hentry] at hinv
  exact mem_iUnion.mpr ⟨a, C a q, mem_image_of_mem (C a) hqZ, -T, hinv.1, hinv.2⟩


theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) : NullInFourCoordinates geometricException := by
  let E := fun n : ℕ => {x | x ∈ physicalPhaseSpace ∧
    (∀ᶠ t in atTop, ∀ i, 1 / (n + 1 : ℝ) ≤
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) ∧ WallProductDecay x}
  have hE : ∀ n, NullInFourCoordinates (E n) := fun n =>
    nullInFourCoordinates_fixed_taub_avoidance hBirkhoff (by positivity)
  apply (nullInFourCoordinates_taubSubspaces.union (NullInFourCoordinates.iUnion hE)).mono
  intro x hx
  by_cases hT : x ∈ taubSubspaces
  · exact Or.inl hT
  · obtain ⟨ε, hε, H⟩ := hx.2.resolve_left hT
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact Or.inr (mem_iUnion.mpr ⟨n, hx.1,
      H.mono (fun t ht i => hn.le.trans (ht i)), hBrehm.wallProductDecay hx.1 hT⟩)

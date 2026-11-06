-- Prove2me | solution 1 for BianchiIX.exists_restartRadialFailure_partition
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:12:16.349195+00:00
-- url     : https://prove2.me/submissions/2668b2c8-a3d0-41e5-9c49-eefcbc63fb18

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_EraCodingData
import Theorems.Thm_BianchiIX_exists_era_joint_statistics
import Theorems.Thm_BianchiIX_exists_mem_physicalRadialPiece
import Theorems.Thm_BianchiIX_exists_restartShear_common_statistical_preparation
import Theorems.Thm_BianchiIX_exists_restart_statistical_preparation
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

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
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

end
end

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_le {d : ℝ} (hd : 0 ≤ d) (j : ℕ) : dyadicScale d j ≤ d :=
  mul_le_of_le_one_right hd (pow_le_one₀ (by norm_num) (by norm_num))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.two_mul_dyadicScale (d : ℝ) (j : ℕ) :
    2 * dyadicScale d j = d * (1 / 2 : ℝ) ^ j := by
  rw [dyadicScale, pow_succ]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_mem_dyadicScale_Ioc {d x : ℝ} (hd : 0 < d) (hx : x ∈ Ioc 0 d) :
    ∃ j : ℕ, x ∈ Ioc (dyadicScale d j) (2 * dyadicScale d j) := by
  obtain ⟨j, hj, hJ⟩ := exists_nat_pow_near_of_lt_one (div_pos hx.1 hd)
    ((div_le_one hd).mpr hx.2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ?_, ?_⟩
  · change d * (1 / 2 : ℝ) ^ (j + 1) < x
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ hd).mp hj)
  · rw [two_mul_dyadicScale]
    exact ((div_le_iff₀ hd).mp hJ).trans_eq (mul_comm _ _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.pairwise_disjoint_dyadicScale_Ioc {d : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun j k : ℕ => Disjoint (Ioc (dyadicScale d j) (2 * dyadicScale d j))
      (Ioc (dyadicScale d k) (2 * dyadicScale d k))) := by
  have H {j k : ℕ} (hjk : j < k) : 2 * dyadicScale d k ≤ dyadicScale d j := by
    rw [two_mul_dyadicScale]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hjk) hd
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hjk with hj | hk
  · exact (not_lt_of_ge (hy.2.trans (H hj))) hx.1
  · exact (not_lt_of_ge (hx.2.trans (H hk))) hy.1

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
open Set

private theorem BianchiIX.mainWallReflection_det : mainWallReflectionEquiv.toLinearMap.det = 1 := by
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' mainWallReflectionEquiv.toLinearMap =
      !![-1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, mainWallReflectionEquiv, mainWallReflectionLinear, mainWallReflection]
  rw [H]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallRadicand_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallRadicand h (mainWallReflection y) = mainWallRadicand h y := by
  dsimp [mainWallRadicand, mainWallReflection, curvature]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.mainWallChart_reflection (h : ℝ) (y : SectionCoordinates) :
    mainWallChart h (mainWallReflection y) = axisSwap (mainWallChart h y) := by
  simp only [mainWallChart, mainWallRadicand_reflection]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_scaledAngularLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hρ : 0 < z 0) (ht : 0 < z 2) :
    HasFDerivAt (scaledAngularLogCoordinates a) (scaledAngularLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z) using 1
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).log hρ.ne').neg using 1
    ext v
    change -(z 0)⁻¹ * v 0 = -((z 0)⁻¹ * v 0)
    ring
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul (2 * a)).log
      (mul_pos (mul_pos (by norm_num) ha) ht).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((2 * a * z 2)⁻¹ * (2 * a * v 2))
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogDifferential_det {z : SectionCoordinates} (hρ : z 0 ≠ 0) :
    (scaledAngularLogDifferential z).det = -(z 2)⁻¹ := by
  change (scaledAngularLogDifferential z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (scaledAngularLogDifferential z).toLinearMap =
      !![z 1, z 0, 0; -(z 0)⁻¹, 0, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, scaledAngularLogDifferential]
  rw [H]
  simp [Matrix.det_fin_three, mul_comm, hρ]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledAngularLogCoordinates a) {z : SectionCoordinates | 0 < z 0 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (z 0) = -Real.log (w 0) at h1
  change -Real.log (2 * a * z 2) = -Real.log (2 * a * w 2) at h2
  have hρ := Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  have ht := Real.log_injOn_pos (mul_pos (mul_pos (by norm_num) ha) hz.2)
    (mul_pos (mul_pos (by norm_num) ha) hw.2) (neg_injective h2)
  have htw : z 2 = w 2 := mul_left_cancel₀ (by positivity : 2 * a ≠ 0) ht
  change z 1 * z 0 = w 1 * w 0 at h0
  rw [hρ] at h0
  have hθ := mul_right_cancel₀ hw.1.ne' h0
  ext i
  fin_cases i
  · exact hρ
  · exact hθ
  · exact htw

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallReflection_image {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallReflection '' A) :=
  hA.image_of_continuousOn_injOn mainWallReflectionEquiv.continuous.continuousOn
    mainWallReflectionEquiv.injective.injOn

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_mainWallOriginalDensity (h : ℝ) : Measurable (mainWallOriginalDensity h) := by
  unfold mainWallOriginalDensity sectionFluxDensity shearSq mainWallChart mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallChartDomain_of_small {h d : ℝ} {z : SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hdh : d ≤ h / 8)
    (hs : |z 0| ≤ d) (hb : Real.exp (-z 1) ≤ d) (hc : Real.exp (-z 2) ≤ d) :
    z ∈ mainWallChartDomain h := by
  have hQ := (abs_le.mp (curvature_abs_le_sum_sq hh.le (Real.exp_pos (-z 1)).le
    (Real.exp_pos (-z 2)).le)).2
  have hsum : h + Real.exp (-z 1) + Real.exp (-z 2) ≤ 5 / 4 * h := by linarith
  have hsum2 := pow_le_pow_left₀ (by positivity : 0 ≤ h + Real.exp (-z 1) + Real.exp (-z 2)) hsum 2
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hs2 : (z 0) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hs.trans (by linarith : d ≤ 1 / 8))
  change 0 < 1 - (z 0) ^ 2 - curvature h (Real.exp (-z 1)) (Real.exp (-z 2))
  nlinarith only [hQ, hsum2, hh2, hs2]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_image {h : ℝ} {A : Set SectionCoordinates}
    {f : SectionCoordinates → SectionCoordinates}
    {f' : SectionCoordinates → SectionCoordinates →L[ℝ] SectionCoordinates}
    (hA : MeasurableSet A) (hd : ∀ z ∈ A, HasFDerivAt f (f' z) z)
    (hi : InjOn f A) (hdom : f '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (f '' A) =
      ∫⁻ z in A, ENNReal.ofReal |(f' z).det| * ENNReal.ofReal (mainWallOriginalDensity h (f z)) := by
  have himage := hA.image_of_continuousOn_injOn
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
  rw [mainWallOriginalMeasure, withDensity_apply _ himage,
    Measure.restrict_restrict_of_subset hdom,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA
      (fun z hz => (hd z hz).hasFDerivWithinAt) hi]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalDensity_reflection (h : ℝ) (z : SectionCoordinates) :
    mainWallOriginalDensity h (mainWallReflection z) = mainWallOriginalDensity h z := by
  unfold mainWallOriginalDensity
  rw [mainWallChart_reflection]
  simp [axisSwap, mainWallReflection, sectionFluxDensity, shearSq]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_reflection {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) :
    mainWallOriginalMeasure h (mainWallReflection '' A) = mainWallOriginalMeasure h A := by
  let D := mainWallChartDomain h
  have hD : MeasurableSet D := (isOpen_mainWallChartDomain h).measurableSet
  have hI : mainWallReflection '' (A ∩ D) = mainWallReflection '' A ∩ D := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by simpa only [D, mainWallChartDomain, mem_ofPred_eq,
        mainWallRadicand_reflection] using hd⟩
    · rintro ⟨⟨x, hx, rfl⟩, hd⟩
      exact ⟨x, ⟨hx, by simpa only [D, mainWallChartDomain, mem_ofPred_eq,
        mainWallRadicand_reflection] using hd⟩, rfl⟩
  have H (B : Set SectionCoordinates) (hB : MeasurableSet B) :
      mainWallOriginalMeasure h B = ∫⁻ y in B ∩ D, ENNReal.ofReal (mainWallOriginalDensity h y) := by
    rw [mainWallOriginalMeasure, withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [H _ (measurableSet_mainWallReflection_image hA), H _ hA, ← hI]
  have hf (y : SectionCoordinates) : HasFDerivAt mainWallReflection
      mainWallReflectionEquiv.toContinuousLinearMap y := mainWallReflectionEquiv.hasFDerivAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hA.inter hD)
    (fun y _ => (hf y).hasFDerivWithinAt) mainWallReflectionEquiv.injective.injOn]
  have hdet : mainWallReflectionEquiv.toContinuousLinearMap.det = 1 := mainWallReflection_det
  simp only [hdet, abs_one, ENNReal.ofReal_one, mainWallOriginalDensity_reflection, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_signedShearLogCoordinates {σ : ℝ} {z : SectionCoordinates}
    (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    HasFDerivAt (signedShearLogCoordinates σ) (signedShearLogDifferential σ z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).const_mul σ
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).log h₁.ne').neg using 1
    ext v
    change -(z 1)⁻¹ * v 1 = -((z 1)⁻¹ * v 1)
    ring
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).log h₂.ne').neg using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((z 2)⁻¹ * v 2)
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearLogDifferential_det (σ : ℝ) (z : SectionCoordinates) :
    (signedShearLogDifferential σ z).det = σ / (z 1 * z 2) := by
  change (signedShearLogDifferential σ z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (signedShearLogDifferential σ z).toLinearMap =
      !![σ, 0, 0; 0, -(z 1)⁻¹, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, signedShearLogDifferential]
  rw [H, Matrix.det_fin_three]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearLogCoordinates_injOn {σ : ℝ} (hσ : σ ≠ 0) :
    InjOn (signedShearLogCoordinates σ) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 : σ * z 0 = σ * w 0 := congrFun heq 0
  have h1 : -Real.log (z 1) = -Real.log (w 1) := congrFun heq 1
  have h2 : -Real.log (z 2) = -Real.log (w 2) := congrFun heq 2
  ext i
  fin_cases i
  · exact mul_left_cancel₀ hσ h0
  · exact Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  · exact Real.log_injOn_pos hz.2 hw.2 (neg_injective h2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_signedShearLogCoordinates {h σ : ℝ} {A : Set SectionCoordinates}
    (hσ : |σ| = 1) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 1 ∧ 0 < z 2)
    (hdom : signedShearLogCoordinates σ '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (signedShearLogCoordinates σ '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / (z 1 * z 2)) *
        ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ z)) := by
  have hσ0 : σ ≠ 0 := by intro heq; simp [heq] at hσ
  rw [mainWallOriginalMeasure_image hA
    (fun z hz => hasFDerivAt_signedShearLogCoordinates (hpos z hz).1 (hpos z hz).2)
    ((signedShearLogCoordinates_injOn hσ0).mono hpos) hdom]
  apply setLIntegral_congr_fun hA
  intro z hz
  dsimp only
  rw [signedShearLogDifferential_det, abs_div, hσ,
    abs_of_pos (mul_pos (hpos z hz).1 (hpos z hz).2)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_orderedAngularLogCoordinates {h : ℝ} {A : Set SectionCoordinates}
    (otherWall : Bool) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 0 ∧ 0 < z 2)
    (hdom : scaledAngularLogCoordinates (1 / 2) '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (orderedAngularLogCoordinates otherWall '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / z 2) *
        ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall z)) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hd (z : SectionCoordinates) (hz : z ∈ A) :=
    hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi := (scaledAngularLogCoordinates_injOn ha).mono hpos
  have hbase : mainWallOriginalMeasure h (scaledAngularLogCoordinates (1 / 2) '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / z 2) *
        ENNReal.ofReal (mainWallOriginalDensity h (scaledAngularLogCoordinates (1 / 2) z)) := by
    rw [mainWallOriginalMeasure_image hA hd hi hdom]
    apply setLIntegral_congr_fun hA
    intro z hz
    dsimp only
    rw [scaledAngularLogDifferential_det (hpos z hz).1.ne', abs_neg,
      abs_of_pos (inv_pos.mpr (hpos z hz).2)]
    simp only [one_div]
  cases otherWall
  · exact hbase
  · have himage := hA.image_of_continuousOn_injOn
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
    change mainWallOriginalMeasure h ((mainWallReflection ∘ scaledAngularLogCoordinates (1 / 2)) '' A) = _
    rw [image_comp, mainWallOriginalMeasure_reflection himage, hbase]
    simp only [orderedAngularLogCoordinates, ↓reduceIte, mainWallOriginalDensity_reflection]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.setLIntegral_three_coordinates {A : Set SectionCoordinates}
    (hA : MeasurableSet A) {f : SectionCoordinates → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in A, f z) = ∫⁻ x : ℝ, ∫⁻ y : ℝ,
      ∫⁻ r in {r : ℝ | ![r, x, y] ∈ A}, f ![r, x, y] := by
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  have hv : Measurable (fun r : ℝ => ![r, x, y]) := by fun_prop
  have hAf : MeasurableSet {r : ℝ | ![r, x, y] ∈ A} := hA.preimage hv
  rw [← lintegral_indicator hAf]
  apply lintegral_congr
  intro r
  by_cases hr : ![r, x, y] ∈ A <;> simp [hr]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearRadialDomain (a d ε : ℝ) : MeasurableSet (shearRadialDomain a d ε) := by
  have h₁ : MeasurableSet {z : SectionCoordinates | 0 < z 1} := measurableSet_lt (by fun_prop) (by fun_prop)
  have h₂ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hm : MeasurableSet {z : SectionCoordinates | max (z 1) (z 2) ≤ ε * z 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  exact h₁.inter (h₂.inter (hr.inter (hm.inter hd)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularRadialDomain (otherWall : Bool) (a d L : ℝ) :
    MeasurableSet (angularRadialDomain otherWall a d L) := by
  have horder : MeasurableSet {z : SectionCoordinates | if otherWall then z 2 < z 0 else z 2 ≤ z 0} := by
    cases otherWall
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hθ : MeasurableSet {z : SectionCoordinates | |z 1| < L} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hζ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hs : MeasurableSet {z : SectionCoordinates | |z 1| * z 0 < d} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact hθ.inter (hζ.inter (hr.inter (horder.inter (hd.inter hs))))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearLogCoordinates_radialDomain_subset_chart {h a d ε σ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hε : ε ≤ 1) (hσ : |σ| = 1) :
    signedShearLogCoordinates σ '' shearRadialDomain a d ε ⊆ mainWallChartDomain h := by
  rintro _ ⟨z, hz, rfl⟩
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hm : max (z 1) (z 2) ≤ z 0 := hz.2.2.2.1.trans (by nlinarith)
  apply mainWallChartDomain_of_small hh hh1 hdh
  · simpa [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr] using hz.2.2.2.2.le
  · simpa [signedShearLogCoordinates, Real.exp_log hz.1] using (le_max_left (z 1) (z 2)).trans (hm.trans hz.2.2.2.2.le)
  · simpa [signedShearLogCoordinates, Real.exp_log hz.2.1] using (le_max_right (z 1) (z 2)).trans (hm.trans hz.2.2.2.2.le)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogCoordinates_radialDomain_subset_chart {h a d L : ℝ}
    (otherWall : Bool) (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8) :
    scaledAngularLogCoordinates (1 / 2) '' angularRadialDomain otherWall a d L ⊆ mainWallChartDomain h := by
  rintro _ ⟨z, hz, rfl⟩
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hζ : z 2 ≤ z 0 := by
    have ho := hz.2.2.2.1
    cases otherWall
    · exact ho
    · exact le_of_lt ho
  apply mainWallChartDomain_of_small hh hh1 hdh
  · simpa [scaledAngularLogCoordinates, abs_mul, abs_of_pos hr] using hz.2.2.2.2.2.le
  · simpa [scaledAngularLogCoordinates, Real.exp_log hr] using hz.2.2.2.2.1.le
  · simpa [scaledAngularLogCoordinates, Real.exp_log hz.2.1] using hζ.trans hz.2.2.2.2.1.le

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearRadialPiece {a d ε σ : ℝ} {F : Set SectionCoordinates}
    (hσ : σ ≠ 0) (hF : MeasurableSet F) :
    MeasurableSet (signedShearLogCoordinates σ '' (shearRadialDomain a d ε ∩ F)) := by
  have hpos : ∀ z ∈ shearRadialDomain a d ε ∩ F, 0 < z 1 ∧ 0 < z 2 :=
    fun _ hz => ⟨hz.1.1, hz.1.2.1⟩
  exact ((measurableSet_shearRadialDomain a d ε).inter hF).image_of_continuousOn_injOn
    (fun z hz => (hasFDerivAt_signedShearLogCoordinates (hpos z hz).1
      (hpos z hz).2).continuousAt.continuousWithinAt)
    ((signedShearLogCoordinates_injOn hσ).mono hpos)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularRadialPiece {a d L : ℝ} {F : Set SectionCoordinates}
    (otherWall : Bool) (ha : 0 < a) (hF : MeasurableSet F) :
    MeasurableSet (orderedAngularLogCoordinates otherWall '' (angularRadialDomain otherWall a d L ∩ F)) := by
  have hpos : ∀ z ∈ angularRadialDomain otherWall a d L ∩ F, 0 < z 0 ∧ 0 < z 2 :=
    fun _ hz => ⟨ha.trans hz.1.2.2.1.1, hz.1.2.1⟩
  have hbase : MeasurableSet (scaledAngularLogCoordinates (1 / 2) ''
      (angularRadialDomain otherWall a d L ∩ F)) :=
    ((measurableSet_angularRadialDomain otherWall a d L).inter hF).image_of_continuousOn_injOn
      (fun z hz => (hasFDerivAt_scaledAngularLogCoordinates (by norm_num) (hpos z hz).1
        (hpos z hz).2).continuousAt.continuousWithinAt)
      ((scaledAngularLogCoordinates_injOn (by norm_num : (0 : ℝ) < 1 / 2)).mono hpos)
  cases otherWall
  · exact hbase
  · change MeasurableSet ((mainWallReflection ∘ scaledAngularLogCoordinates (1 / 2)) '' _)
    rw [image_comp]
    exact measurableSet_mainWallReflection_image hbase

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.angularRadialPieces_disjoint {a b d e L M : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (orderedAngularLogCoordinates false '' angularRadialDomain false a d L)
      (orderedAngularLogCoordinates true '' angularRadialDomain true b e M) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [orderedAngularLogCoordinates, Bool.false_eq_true, ↓reduceIte,
    mainWallReflection, scaledAngularLogCoordinates, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_zero] at h1 h2
  norm_num at h1 h2
  have h10 : y 2 = x 0 := Real.log_injOn_pos hy.2.1 hx0 h1
  have h20 : y 0 = x 2 := Real.log_injOn_pos hy0 hx.2.1 h2
  have hxy : x 2 ≤ x 0 := hx.2.2.2.1
  have hyx : y 2 < y 0 := hy.2.2.2.1
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearRadialPieces_disjoint {a b d e ε δ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (signedShearLogCoordinates 1 '' shearRadialDomain a d ε)
      (signedShearLogCoordinates (-1) '' shearRadialDomain b e δ) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h0 : (-1 : ℝ) * y 0 = 1 * x 0 := congrFun heq 0
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_shearRadialPiece {h a d ε σ : ℝ} {F : Set SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hε : ε ≤ 1) (hσ : |σ| = 1) (hF : MeasurableSet F) :
    mainWallOriginalMeasure h (signedShearLogCoordinates σ '' (shearRadialDomain a d ε ∩ F)) =
      ∫⁻ n₂ : ℝ, ∫⁻ n₃ : ℝ, ENNReal.ofReal (1 / (n₂ * n₃)) *
        ∫⁻ r in {r : ℝ | 0 < n₂ ∧ 0 < n₃ ∧
          r ∈ shearRadialInterval a d ε n₂ n₃ ∧ ![r, n₂, n₃] ∈ F},
          ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ ![r, n₂, n₃])) := by
  have hA := (measurableSet_shearRadialDomain a d ε).inter hF
  rw [mainWallOriginalMeasure_signedShearLogCoordinates hσ hA
    (fun z hz => ⟨hz.1.1, hz.1.2.1⟩)
    ((image_mono inter_subset_left).trans
      (signedShearLogCoordinates_radialDomain_subset_chart hh hh1 ha hdh hε hσ))]
  have hf : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / (z 1 * z 2)) *
      ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ z))) := by
    have hw : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / (z 1 * z 2))) := by fun_prop
    exact hw.mul (((measurable_mainWallOriginalDensity h).comp
      (by unfold signedShearLogCoordinates; fun_prop)).ennreal_ofReal)
  rw [setLIntegral_three_coordinates hA hf]
  apply lintegral_congr
  intro n₂
  apply lintegral_congr
  intro n₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  congr 1
  ext r
  simp [shearRadialDomain, and_assoc]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_angularRadialPiece {h a d L : ℝ} {F : Set SectionCoordinates}
    (otherWall : Bool) (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hF : MeasurableSet F) :
    mainWallOriginalMeasure h
        (orderedAngularLogCoordinates otherWall '' (angularRadialDomain otherWall a d L ∩ F)) =
      ∫⁻ θ : ℝ, ∫⁻ ζ : ℝ, ENNReal.ofReal (1 / ζ) *
        ∫⁻ r in {r : ℝ | |θ| < L ∧ 0 < ζ ∧
          r ∈ angularRadialInterval otherWall a d θ ζ ∧ ![r, θ, ζ] ∈ F},
          ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall ![r, θ, ζ])) := by
  have hA := (measurableSet_angularRadialDomain otherWall a d L).inter hF
  rw [mainWallOriginalMeasure_orderedAngularLogCoordinates otherWall hA
    (fun z hz => ⟨ha.trans hz.1.2.2.1.1, hz.1.2.1⟩)
    ((image_mono inter_subset_left).trans
      (scaledAngularLogCoordinates_radialDomain_subset_chart otherWall hh hh1 ha hdh))]
  have hf : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / z 2) *
      ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall z))) := by
    have hw : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / z 2)) := by fun_prop
    have hc : Measurable (orderedAngularLogCoordinates otherWall) := by
      unfold orderedAngularLogCoordinates scaledAngularLogCoordinates mainWallReflection
      cases otherWall with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; fun_prop
      | true => simp only [↓reduceIte]; fun_prop
    exact hw.mul (((measurable_mainWallOriginalDensity h).comp hc).ennreal_ofReal)
  rw [setLIntegral_three_coordinates hA hf]
  apply lintegral_congr
  intro θ
  apply lintegral_congr
  intro ζ
  simp only [Matrix.cons_val_two]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  congr 1
  ext r
  simp [angularRadialDomain, and_assoc]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialPieceInverse_map {d ε : ℝ} (hd : 0 < d) {i : RadialPieceIndex}
    {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i) :
    radialPieceInverse i.1 (radialPieceMap i.1 z) = z := by
  rcases i with ⟨neg | other, j⟩
  · have h₁ : 0 < z 1 := hz.1
    have h₂ : 0 < z 2 := hz.2.1
    cases neg <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, signedShearLogCoordinates, Real.exp_log h₁, Real.exp_log h₂]
  · have hr : 0 < z 0 := (dyadicScale_pos hd j).trans hz.2.2.1.1
    have hζ : 0 < z 2 := hz.2.1
    cases other <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_log hr, Real.exp_log hζ, hr.ne']

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_mainWallOpenSection (d : ℝ) : MeasurableSet (mainWallOpenSection d) := by
  have hs : MeasurableSet {z : SectionCoordinates | |z 0| < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm : MeasurableSet {z : SectionCoordinates | max (Real.exp (-z 1)) (Real.exp (-z 2)) < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact hs.inter hm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurable_mainWallRadialRadius (ε : ℝ) : Measurable (mainWallRadialRadius ε) := by
  have hS : MeasurableSet {z : SectionCoordinates |
      max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0|} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact Measurable.ite hS (by fun_prop) (by fun_prop)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallRadialRadius_pos {ε : ℝ} (hε : 0 < ε) (z : SectionCoordinates) :
    0 < mainWallRadialRadius ε z := by
  have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  unfold mainWallRadialRadius
  split_ifs with hs
  · exact (mul_pos_iff_of_pos_left hε).mp (hm.trans_le hs)
  · exact hm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallRadialRadius_lt {d ε : ℝ} {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d) : mainWallRadialRadius ε z < d := by
  unfold mainWallRadialRadius
  split_ifs
  · exact hz.1
  · exact hz.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.signedShearLogCoordinates_radial_data {a d ε σ : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hz : z ∈ shearRadialDomain a d ε) :
    |signedShearLogCoordinates σ z 0| = z 0 ∧
    max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) = max (z 1) (z 2) := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  simp [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr,
    Real.exp_log hz.1, Real.exp_log hz.2.1]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.orderedAngularLogCoordinates_radial_data {a d L : ℝ} {z : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hz : z ∈ angularRadialDomain other a d L) :
    |orderedAngularLogCoordinates other z 0| = |z 1| * z 0 ∧
    max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
      (Real.exp (-(orderedAngularLogCoordinates other z) 2)) = z 0 := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho := hz.2.2.2.1
  cases other with
  | false =>
    simp [orderedAngularLogCoordinates, scaledAngularLogCoordinates, abs_mul, abs_of_pos hr,
      Real.exp_log hr, Real.exp_log hz.2.1, max_eq_left ho]
  | true =>
    simp [orderedAngularLogCoordinates, mainWallReflection, scaledAngularLogCoordinates,
      abs_mul, abs_of_pos hr, Real.exp_log hr, Real.exp_log hz.2.1,
      max_eq_right (le_of_lt ho)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearRadialPiece_region {a d ε σ : ℝ} {y : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hy : y ∈ signedShearLogCoordinates σ '' shearRadialDomain a d ε) :
    max (Real.exp (-y 1)) (Real.exp (-y 2)) ≤ ε * |y 0| ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha hσ hz
  have hreg : max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) ≤ ε * |signedShearLogCoordinates σ z 0| := by
    rw [hs, hm]
    exact hz.2.2.2.1
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_pos hreg, hs]
  exact hz.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.angularRadialPiece_region {a d ε : ℝ} {y : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hε : 0 < ε)
    (hy : y ∈ orderedAngularLogCoordinates other '' angularRadialDomain other a d (1 / ε)) :
    ε * |y 0| < max (Real.exp (-y 1)) (Real.exp (-y 2)) ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other ha hz
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hθ : ε * |z 1| < 1 := by
    have H := (lt_div_iff₀ hε).mp hz.1
    nlinarith
  have hreg : ε * |orderedAngularLogCoordinates other z 0| <
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) := by
    rw [hs, hm]
    nlinarith [mul_lt_mul_of_pos_right hθ hr]
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_neg (not_le.mpr hreg), hm]
  exact hz.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_radius {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ physicalRadialPiece d ε i) :
    mainWallRadialRadius ε z ∈ Ioo (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
  rcases i with ⟨neg | other, j⟩
  · exact (shearRadialPiece_region (dyadicScale_pos hd j)
      (by cases neg <;> norm_num) hz).2
  · exact (angularRadialPiece_region other (dyadicScale_pos hd j) hε hz).2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (i : RadialPieceIndex) : physicalRadialPiece d ε i ⊆ mainWallOpenSection d := by
  rcases i with ⟨neg | other, j⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ha := dyadicScale_pos hd j
    obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha
      (show |(if neg then -1 else 1 : ℝ)| = 1 by cases neg <;> norm_num) hz
    change |signedShearLogCoordinates _ z 0| < d ∧
      max (Real.exp (-(signedShearLogCoordinates _ z) 1))
        (Real.exp (-(signedShearLogCoordinates _ z) 2)) < d
    rw [hs, hm]
    refine ⟨hz.2.2.2.2, (hz.2.2.2.1.trans ?_).trans_lt hz.2.2.2.2⟩
    have hr : 0 < z 0 := ha.trans hz.2.2.1.1
    nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other (dyadicScale_pos hd j) hz
    change |orderedAngularLogCoordinates other z 0| < d ∧
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) < d
    rw [hs, hm]
    exact ⟨hz.2.2.2.2.2, hz.2.2.2.2.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shear_angular_radialPieces_disjoint {a b d e ε : ℝ} {σ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hσ : |σ| = 1) (other : Bool) :
    Disjoint (signedShearLogCoordinates σ '' shearRadialDomain a d ε)
      (orderedAngularLogCoordinates other '' angularRadialDomain other b e (1 / ε)) := by
  apply Set.disjoint_left.mpr
  intro z hs ha'
  exact (not_lt_of_ge (shearRadialPiece_region ha hσ hs).1)
    (angularRadialPiece_region other hb hε ha').1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPieces_pairwiseDisjoint {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    Pairwise (fun i j : RadialPieceIndex => Disjoint (physicalRadialPiece d ε i) (physicalRadialPiece d ε j)) := by
  rintro ⟨k, n⟩ ⟨l, m⟩ hij
  by_cases hnm : n = m
  · subst m
    have hkl : k ≠ l := by intro h; exact hij (by cases h; rfl)
    rcases k with neg | other <;> rcases l with neg' | other'
    · cases neg <;> cases neg'
      · exact False.elim (hkl rfl)
      · exact signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
    · exact shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg <;> norm_num) other'
    · exact (shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg' <;> norm_num) other).symm
    · cases other <;> cases other'
      · exact False.elim (hkl rfl)
      · exact angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
  · apply Set.disjoint_left.mpr
    intro z hz hw
    exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd.le hnm)
      ⟨(physicalRadialPiece_radius hd hε hz).1, (physicalRadialPiece_radius hd hε hz).2.le⟩
      ⟨(physicalRadialPiece_radius hd hε hw).1, (physicalRadialPiece_radius hd hε hw).2.le⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.measurableSet_mainWallRadialBoundary (d ε : ℝ) : MeasurableSet (mainWallRadialBoundary d ε) :=
  (measurableSet_mainWallOpenSection d).inter (MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_mainWallRadialRadius ε) measurable_const)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionCoordinate_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | z i = t} = 0 := by
  exact Measure.pi_eval_preimage_null (fun _ : Fin 3 => (volume : Measure ℝ)) (measure_singleton t)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_sectionWall_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | Real.exp (-z i) = t} = 0 := by
  apply measure_mono_null (t := {z : SectionCoordinates | z i = -Real.log t})
    _ (volume_sectionCoordinate_level i _)
  intro z hz
  have H := congrArg Real.log hz
  rw [Real.log_exp] at H
  change z i = -Real.log t
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_mainWallRadialRadius_level (ε t : ℝ) :
    volume {z : SectionCoordinates | mainWallRadialRadius ε z = t} = 0 := by
  have hnull : volume (({z : SectionCoordinates | z 0 = t} ∪ {z | z 0 = -t}) ∪
      ({z | Real.exp (-z 1) = t} ∪ {z | Real.exp (-z 2) = t})) = 0 :=
    measure_union_null (measure_union_null (volume_sectionCoordinate_level 0 t)
      (volume_sectionCoordinate_level 0 (-t)))
      (measure_union_null (volume_sectionWall_level 1 t) (volume_sectionWall_level 2 t))
  apply measure_mono_null _ hnull
  intro z hz
  change mainWallRadialRadius ε z = t at hz
  unfold mainWallRadialRadius at hz
  split_ifs at hz
  · apply Or.inl
    rcases le_total 0 (z 0) with hs | hs
    · exact Or.inl (by simpa only [mem_ofPred_eq, abs_of_nonneg hs] using hz)
    · exact Or.inr (by rw [abs_of_nonpos hs] at hz; change z 0 = -t; linarith)
  · apply Or.inr
    rcases le_total (Real.exp (-z 1)) (Real.exp (-z 2)) with hw | hw
    · exact Or.inr (by simpa only [mem_ofPred_eq, max_eq_right hw] using hz)
    · exact Or.inl (by simpa only [mem_ofPred_eq, max_eq_left hw] using hz)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.volume_mainWallRadialBoundary (d ε : ℝ) : volume (mainWallRadialBoundary d ε) = 0 :=
  measure_mono_null inter_subset_right (measure_iUnion_null fun _ => volume_mainWallRadialRadius_level _ _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallOriginalMeasure_radialBoundary (h d ε : ℝ) :
    mainWallOriginalMeasure h (mainWallRadialBoundary d ε) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallRadialBoundary d ε)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallOpenSection_radial_partition {d ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    mainWallOpenSection d = mainWallRadialBoundary d ε ∪ ⋃ i : RadialPieceIndex, physicalRadialPiece d ε i := by
  ext z
  constructor
  · intro hz
    by_cases hb : z ∈ mainWallRadialBoundary d ε
    · exact Or.inl hb
    · obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd
        ⟨mainWallRadialRadius_pos hε z, (mainWallRadialRadius_lt hz).le⟩
      have hne : mainWallRadialRadius ε z ≠ 2 * dyadicScale d j := by
        intro heq
        exact hb ⟨hz, mem_iUnion_of_mem j heq⟩
      obtain ⟨k, hk⟩ := exists_mem_physicalRadialPiece hε hz ⟨hj.1, lt_of_le_of_ne hj.2 hne⟩
      exact Or.inr (mem_iUnion_of_mem (k, j) hk)
  · rintro (hb | hp)
    · exact hb.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact physicalRadialPiece_subset_openSection hd hε1 i hi

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailurePiece_subset (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : radialFailurePiece d ε F i ⊆ physicalRadialPiece d ε i :=
  image_mono inter_subset_left

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_radialFailurePiece {d ε : ℝ} (hd : 0 < d)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i))
    (i : RadialPieceIndex) : MeasurableSet (radialFailurePiece d ε F i) := by
  rcases i with ⟨neg | other, j⟩
  · exact measurableSet_shearRadialPiece (by cases neg <;> norm_num) (hF _)
  · exact measurableSet_angularRadialPiece other (dyadicScale_pos hd j) (hF _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_radialFailureSet {d ε : ℝ} (hd : 0 < d)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i)) :
    MeasurableSet (radialFailureSet d ε F) :=
  (measurableSet_mainWallRadialBoundary d ε).union
    (MeasurableSet.iUnion fun i => measurableSet_radialFailurePiece hd hF i)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailurePieces_pairwiseDisjoint {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (F : RadialPieceIndex → Set SectionCoordinates) :
    Pairwise (fun i j : RadialPieceIndex => Disjoint (radialFailurePiece d ε F i) (radialFailurePiece d ε F j)) := by
  intro i j hij
  exact (physicalRadialPieces_pairwiseDisjoint hd hε hij).mono
    (radialFailurePiece_subset d ε F i) (radialFailurePiece_subset d ε F j)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_radialFailurePiece {h d ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8) (hε : ε ≤ 1)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i))
    (i : RadialPieceIndex) :
    mainWallOriginalMeasure h (radialFailurePiece d ε F i) = radialFailureIntegral h d ε F i := by
  rcases i with ⟨neg | other, j⟩
  · exact mainWallOriginalMeasure_shearRadialPiece hh hh1 (dyadicScale_pos hd j) hdh hε
      (by cases neg <;> norm_num) (hF _)
  · exact mainWallOriginalMeasure_angularRadialPiece other hh hh1 (dyadicScale_pos hd j) hdh (hF _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallOriginalMeasure_radialFailureSet {h d ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {F : RadialPieceIndex → Set SectionCoordinates}
    (hF : ∀ i, MeasurableSet (F i)) :
    mainWallOriginalMeasure h (radialFailureSet d ε F) = ∑' i, radialFailureIntegral h d ε F i := by
  have H : mainWallOriginalMeasure h (radialFailureSet d ε F) =
      mainWallOriginalMeasure h (⋃ i, radialFailurePiece d ε F i) := by
    apply le_antisymm
    · exact (measure_union_le _ _).trans_eq (by rw [mainWallOriginalMeasure_radialBoundary, zero_add])
    · exact measure_mono subset_union_right
  rw [H, measure_iUnion (radialFailurePieces_pairwiseDisjoint hd hε F)
    (fun i => measurableSet_radialFailurePiece hd hF i)]
  apply tsum_congr
  exact fun i => mainWallOriginalMeasure_radialFailurePiece hh hh1 hd hdh hε1 hF i

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailureSet_complement {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d \ radialFailureSet d ε F) :
    ∃! i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧ radialPieceInverse i.1 z ∉ F i := by
  have hb : z ∉ mainWallRadialBoundary d ε := fun hb => hz.2 (Or.inl hb)
  have hcover := hz.1
  rw [mainWallOpenSection_radial_partition hd hε hε1] at hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.resolve_left hb)
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · rintro hf
    rcases hi with ⟨x, hx, rfl⟩
    rw [radialPieceInverse_map hd hx] at hf
    exact hz.2 (Or.inr (mem_iUnion_of_mem i ⟨x, ⟨hx, hf⟩, rfl⟩))
  · intro j hj
    by_contra hji
    exact Set.disjoint_left.mp (physicalRadialPieces_pairwiseDisjoint hd hε hji) hj.1 hi

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartLabelSet (L r P : ℝ) : MeasurableSet (restartLabelSet L r P) :=
  (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartShearCommonLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearCommonLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le (measurable_fst.min measurable_snd) measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.era_radial_good_iff {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ}
    {Y : CoreAngleState} {x : ℝ} (hx : x ∈ Ioo 0 1) (hmatch : Γ.state (2 / x) = Y) :
    x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap ↔ (B, Y) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  change (x ∈ Ioo 0 1 ∧ (B, Γ.state (2 / x)) ∈ EraSurvivor.typicalDomain η J σ Bcap) ↔ _
  rw [hmatch]
  exact and_iff_right hx

end
end

private theorem BianchiIX.measurableSet_labelRadialFailure {a : ℝ} {L : Set (ℝ × ℝ)}
    {G : Set (ℝ × CoreAngleState)} {Z : (ℝ × ℝ) → ℝ → ℝ × CoreAngleState}
    (hL : MeasurableSet L) (hG : MeasurableSet G)
    (hZ : Measurable (fun p : L × Icc a (2 * a) => Z p.1.val p.2.val)) :
    MeasurableSet (labelRadialFailure a L G Z) := by
  let D : Set SectionCoordinates := {z | (z 1, z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a)}
  have hl : Measurable (fun z : SectionCoordinates => (z 1, z 2)) := by fun_prop
  have hD : MeasurableSet D := (hL.preimage hl).inter
    (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let f : D → L × Icc a (2 * a) := fun z =>
    (⟨(z.val 1, z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hf : Measurable f := by
    apply Measurable.prodMk
    · exact (hl.comp measurable_subtype_coe).subtype_mk
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hG.compl.preimage (hZ.comp hf))
  have heq : Subtype.val '' (fun z : D => Z (z.val 1, z.val 2) (z.val 0)) ⁻¹' Gᶜ =
      {z : SectionCoordinates | (z 1, z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a) ∧ Z (z 1, z 2) (z 0) ∉ G} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, w.property.2, hw⟩
    · rintro ⟨hl', hr, hg⟩
      exact ⟨⟨z, hl', hr⟩, hg, rfl⟩
  change MeasurableSet (Subtype.val '' (fun z : D => Z (z.val 1, z.val 2) (z.val 0)) ⁻¹' Gᶜ) at H
  rw [heq] at H
  have hU : MeasurableSet {z : SectionCoordinates | z 0 ∈ Icc a (2 * a) ∧ (z 1, z 2) ∉ L} :=
    (measurableSet_Icc.preimage (measurable_pi_apply 0)).inter (hL.preimage hl).compl
  convert! hU.union H using 1
  ext z
  simp only [labelRadialFailure, mem_union, mem_ofPred_eq]
  tauto

private theorem BianchiIX.restartRadialFailure_good {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i)
    (hn : z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i) :
    restartRadialOutput h q d ε i z ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  by_contra hbad
  apply hn
  rcases i with ⟨neg | other, j⟩
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    cases neg <;> exact ⟨hr, Or.inr hbad⟩
  · exact ⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, Or.inr hbad⟩

private theorem BianchiIX.restartRadialFailureSet_success {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d \
      radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) :
    ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
      restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  obtain ⟨i, ⟨hi, hn⟩, _⟩ := radialFailureSet_complement hd hε hε1 _ hz
  refine ⟨i, hi, ?_⟩
  rcases hi with ⟨x, hx, rfl⟩
  rw [radialPieceInverse_map hd hx] at hn ⊢
  exact restartRadialFailure_good hx hn

/-- The selected and unselected statistical fibers instantiate the exact countable flux identity. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                (∀ i, MeasurableSet (F i)) ∧ MeasurableSet (radialFailureSet d ε F) ∧
                  mainWallOriginalMeasure h (radialFailureSet d ε F) = (∑' i, radialFailureIntegral h d ε F i) ∧
                    (∀ z ∈ mainWallOpenSection d \ radialFailureSet d ε F,
                      ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
                        restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈
                          EraSurvivor.typicalDomain η J σ Bcap) ∧
                    ∀ i z, z ∈ radialPieceDomain d ε i → z ∉ F i →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = restartRadialOutput h q d ε i z ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  obtain ⟨hS, hhS, HS⟩ := exists_restartShear_common_statistical_preparation
  obtain ⟨hA, hhA, HA⟩ := exists_restart_statistical_preparation
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hG, Bs, hBs, _, Hstats⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hS (min hA (1 / 8)),
    lt_min hhS (lt_min hhA (by norm_num)), (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro h hh q D P hq hD hP ε hε
  have hh1 : h ≤ 1 / 8 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨aS, haS, HShear⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP Bs hBs
  obtain ⟨aA, haA, HAngle⟩ := HA h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    (1 / ε) (by positivity [hε.1]) q P hq (by linarith only [hD, hP]) Bs hBs
  refine ⟨min aS (min aA (h / 8)), lt_min haS (lt_min haA (div_pos hh.1 (by norm_num))),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro d hd F
  have hdh : d ≤ h / 8 := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have HF : ∀ i, MeasurableSet (F i) := by
    rintro ⟨neg | other, j⟩
    · have ha : dyadicScale d j ∈ Ioc (0 : ℝ) aS :=
        ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
      have H := measurableSet_labelRadialFailure
        (Z := fun l r => (restartShearAmplitudeBudget (dyadicScale d j) l.1 l.2,
          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) l.1 l.2 r))
        (measurableSet_restartShearCommonLabelSet ε (dyadicScale d j) P) hG
        (HShear (dyadicScale d j) ha ε ⟨hε.1.le, hε.2⟩).1
      cases neg
      · exact H
      · exact H.preimage (by fun_prop)
    · have ha : dyadicScale d j ∈ Ioc (0 : ℝ) aA :=
        ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans
          (hd.2.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
      exact measurableSet_labelRadialFailure
        (Z := fun l r => (restartAmplitudeBudget (1 / ε) (dyadicScale d j) l.2,
          restartReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) l.1 l.2 r))
        (measurableSet_restartLabelSet (1 / ε) (dyadicScale d j) P) hG
        (HAngle (dyadicScale d j) ha).1
  refine ⟨HF, measurableSet_radialFailureSet hd.1 HF,
    mainWallOriginalMeasure_radialFailureSet hh.1 hh1 hd.1 hdh hε.1 (by linarith only [hε.2]) HF,
    (fun _ hz => restartRadialFailureSet_success hd.1 hε.1 (by linarith only [hε.2]) hz), ?_⟩
  have HShearStats (j : ℕ) (n₂ n₃ r : ℝ)
      (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε (dyadicScale d j) P)
      (hr : r ∈ Icc (dyadicScale d j) (2 * dyadicScale d j))
      (hg : (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
        restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) n₂ n₃ r) ∈
          EraSurvivor.typicalDomain η J σ Bcap) :
      ∃ p : eraSurvivorDomain η J σ Bcap,
        p.val = (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) n₂ n₃ r) ∧
        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
    obtain ⟨hB, hΓ, Hrad⟩ := (HShear (dyadicScale d j)
      ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
      ε ⟨hε.1.le, hε.2⟩).2 n₂ n₃ hl.1 hl.2.1 hl.2.2
    obtain ⟨_, _, _, Hgood⟩ := Hstats _ hB _ hΓ
    obtain ⟨p, hp, hs⟩ := Hgood _ ((era_radial_good_iff (Hrad r hr).1 (Hrad r hr).2.2.2).mpr hg)
    exact ⟨p, hp.trans (congrArg (fun Z => (_, Z)) (Hrad r hr).2.2.2), hs⟩
  rintro ⟨neg | other, j⟩ z hz hn
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    have hg := restartRadialFailure_good hz hn
    cases neg
    · exact HShearStats j (z 1) (z 2) (z 0)
        (by by_contra hl; exact hn ⟨hr, Or.inl hl⟩) hr hg
    · exact HShearStats j (z 2) (z 1) (z 0)
        (by by_contra hl; exact hn ⟨hr, Or.inl hl⟩) hr hg
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    have hl : (z 1, z 2) ∈ restartLabelSet (1 / ε) (dyadicScale d j) P := by
      by_contra hl
      exact hn ⟨hr, Or.inl hl⟩
    obtain ⟨hB, hΓ, Hrad⟩ := (HAngle (dyadicScale d j)
      ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans
        (hd.2.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩).2 (z 1) (z 2) hl.1 hl.2
    obtain ⟨_, _, _, Hgood⟩ := Hstats _ hB _ hΓ
    obtain ⟨p, hp, hs⟩ := Hgood _
      ((era_radial_good_iff (Hrad (z 0) hr).1 (Hrad (z 0) hr).2.2.2).mpr (restartRadialFailure_good hz hn))
    exact ⟨p, hp.trans (congrArg (fun Z => (_, Z)) (Hrad (z 0) hr).2.2.2), hs⟩

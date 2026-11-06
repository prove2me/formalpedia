-- Prove2me | solution 1 for BianchiIX.exists_axisWall_coordinate_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:36:16.434594+00:00
-- url     : https://prove2.me/submissions/9799be04-5518-4bd4-9ff9-e1f24643a5c4

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_NormalizedSymmetry_sectionFlux
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_hasFDerivAt_normalizedMaxCurve
import Theorems.Thm_BianchiIX_mainWallChart_signed_flux
import Theorems.Thm_BianchiIX_normalizedSectionFlux_add_flow
import Theorems.Thm_BianchiIX_normalizedSectionFlux_flow
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_eq_exp_integral
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

private theorem BianchiIX.contDiffAt_mainWallCoordinates {x : NormalizedState} (hx : positiveWalls x)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n mainWallCoordinates x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 5) x
  · exact ((contDiffAt_apply ℝ ℝ (3 : Fin 5) x).log (ne_of_gt hx.2.1)).neg
  · exact ((contDiffAt_apply ℝ ℝ (4 : Fin 5) x).log (ne_of_gt hx.2.2)).neg

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

private theorem BianchiIX.mainWallChart_flux {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    |normalizedSectionFlux (mainWallChart h y) (mainWallChartFrame h y)| = mainWallChartDensity h y := by
  rw [mainWallChart_signed_flux hh hy, abs_neg, abs_of_pos (mainWallChartDensity_pos hh hy)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mainWallChart_flux_linear {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) (L : SectionCoordinates →L[ℝ] SectionCoordinates) :
    |normalizedSectionFlux (mainWallChart h y)
        (fun i => mainWallChartDifferential h y (L (Pi.single i 1)))| =
      mainWallChartDensity h y * |L.det| := by
  let x := mainWallChart h y
  let f : SectionCoordinates [⋀^Fin 3]→ₗ[ℝ] ℝ :=
    (normalizedVolumeWeight x)⁻¹ •
      ((normalizedAmbientVolume.curryLeft ((1 / 2 : ℝ) • x)).curryLeft (normalizedField x)).compLinearMap
        (mainWallChartDifferential h y).toLinearMap
  let b := Pi.basisFun ℝ (Fin 3)
  have hd : b.det (L ∘ b) = L.det := by
    convert! b.det_comp L.toLinearMap b using 1
    simp only [b.det_self, mul_one]
  have H : f (L ∘ b) = L.det * f b := by
    calc
      f (L ∘ b) = (f b • b.det) (L ∘ b) := congrArg (fun a => a (L ∘ b)) (f.eq_smul_basis_det b)
      _ = L.det * f b := by
        change f b * b.det (L ∘ b) = L.det * f b
        rw [hd, mul_comm]
  have hf (v : Fin 3 → SectionCoordinates) :
      f v = normalizedSectionFlux x (fun i => mainWallChartDifferential h y (v i)) := by
    simp only [f, AlternatingMap.smul_apply, AlternatingMap.compLinearMap_apply,
      AlternatingMap.curryLeft_apply_apply, smul_eq_mul,
      normalizedSectionFlux, normalizedConstraintVolume, div_eq_mul_inv]
    rw [mul_comm]
    congr 1
  rw [hf, hf] at H
  have heq : normalizedSectionFlux x (fun i => mainWallChartDifferential h y (L (Pi.single i 1))) =
      L.det * normalizedSectionFlux x (mainWallChartFrame h y) := by
    simp only [b, Pi.basisFun_apply, Function.comp_apply] at H
    convert! H using 1
  rw [heq, abs_mul, mainWallChart_flux hh hy, mul_comm]

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

private theorem BianchiIX.contDiffAt_axisWallCoordinates (A : NormalizedSymmetry) {x : NormalizedState}
    (hx : positiveWalls x) (n : WithTop ℕ∞) : ContDiffAt ℝ n (axisWallCoordinates A) x :=
  (contDiffAt_mainWallCoordinates ((A.positive x).mpr hx) n).comp x A.map.contDiff.contDiffAt

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

private theorem BianchiIX.axisWallChartDifferential_tangent (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    (normalizedConstraintDifferential (axisWallChart A h y)).comp (axisWallChartDifferential A h y) = 0 := by
  have hd : HasFDerivAt (axisWallChart A h) (axisWallChartDifferential A h y) y :=
    ((contDiffAt_axisWallChart A hy 1).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hasFDerivAt_stateConstraint (axisWallChart A h y)).comp y hd
  have heq : (fun _ : SectionCoordinates => (1 : ℝ)) =ᶠ[𝓝 y]
      (fun z => stateConstraint (axisWallChart A h z)) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy] with z hz
    exact (axisWallChart_constraint A hz).symm
  exact (H.congr_of_eventuallyEq heq).unique (hasFDerivAt_const 1 y)

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
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_flux_linear (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) (L : SectionCoordinates →L[ℝ] SectionCoordinates) :
    |normalizedSectionFlux (axisWallChart A h y)
        (fun i => axisWallChartDifferential A h y (L (Pi.single i 1)))| =
      mainWallChartDensity h y * |L.det| := by
  rw [axisWallChartDifferential_eq A hy]
  have H := A.symm.sectionFlux (mainWallChart h y)
    (fun i => mainWallChartDifferential h y (L (Pi.single i 1)))
  exact (congrArg abs H).trans (mainWallChart_flux_linear hh hy L)

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

private theorem BianchiIX.axisWallChartFrame_tangent (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (i : Fin 3) :
    normalizedConstraintDifferential (axisWallChart A h y) (axisWallChartFrame A h y i) = 0 :=
  congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1))
    (axisWallChartDifferential_tangent A hy)

private theorem BianchiIX.axisWallChart_flux (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    |normalizedSectionFlux (axisWallChart A h y) (axisWallChartFrame A h y)| = mainWallChartDensity h y := by
  rw [axisWallChart_signed_flux A hh hy, abs_neg, abs_of_pos (mainWallChartDensity_pos hh hy)]

private theorem BianchiIX.axisWall_coordinate_jacobian (A B : NormalizedSymmetry) {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hτ : DifferentiableAt ℝ τ (axisWallChart A h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v)))) :
    mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
      Real.exp (∫ u in t₀..τ (axisWallChart A h y),
        normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
          mainWallChartDensity h y := by
  let F := fun x => normalizedMaxCurve x t₀ (τ x)
  have hdF := (hasFDerivAt_normalized_arrival ht hτ).differentiableAt.hasFDerivAt
  have hdsource := ((contDiffAt_axisWallChart A hy 1).differentiableAt (by norm_num)).hasFDerivAt
  have hdtarget := ((contDiffAt_axisWallChart B hRy 1).differentiableAt (by norm_num)).hasFDerivAt
  have hder : (axisWallChartDifferential B k (R y)).comp (fderiv ℝ R y) =
      (fderiv ℝ F (axisWallChart A h y)).comp (axisWallChartDifferential A h y) :=
    (hdtarget.comp y hR.hasFDerivAt).unique ((hdF.comp y hdsource).congr_of_eventuallyEq heq)
  have hframe : (fun i => fderiv ℝ F (axisWallChart A h y) (axisWallChartFrame A h y i)) =
      (fun i => axisWallChartDifferential B k (R y) (fderiv ℝ R y (Pi.single i 1))) := by
    funext i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] NormalizedState => L (Pi.single i 1)) hder.symm
  have H := normalizedSectionFlux_arrival_abs (axisWallChart_positive A hh y)
    (axisWallChart_constraint A hy) ht hτ (axisWallChartFrame A h y) (axisWallChartFrame_tangent A hy)
  have hvalue : axisWallChart B k (R y) =
      normalizedMaxCurve (axisWallChart A h y) t₀ (τ (axisWallChart A h y)) := by
    convert! heq.self_of_nhds using 1
  rw [← hvalue] at H
  rw [show (fun i => fderiv ℝ (fun x => normalizedMaxCurve x t₀ (τ x)) (axisWallChart A h y)
      (axisWallChartFrame A h y i)) = _ from hframe,
    axisWallChart_flux_linear B hk hRy, axisWallChart_flux A hh hy] at H
  exact H

private theorem BianchiIX.axisWall_coordinate_det_ne_zero (A B : NormalizedSymmetry) {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hτ : DifferentiableAt ℝ τ (axisWallChart A h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v)))) :
    (fderiv ℝ R y).det ≠ 0 := by
  have H := axisWall_coordinate_jacobian A B hh hk hy hRy ht hτ hR heq
  intro hz
  rw [hz, abs_zero, mul_zero] at H
  exact (ne_of_gt (mul_pos (Real.exp_pos _) (mainWallChartDensity_pos hh hy))) H.symm


/-- Every actual crossing between two axis charts has locally unique smooth event coordinates. -/
theorem solution (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (ht : t ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ (τ : NormalizedState → ℝ) (R : SectionCoordinates → SectionCoordinates),
      τ (axisWallChart A h y) = t ∧ ContDiffAt ℝ 1 τ (axisWallChart A h y) ∧
      ContDiffAt ℝ 1 R y ∧ R y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      (∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
        τ (axisWallChart A h v) ∈ normalizedMaxDomain (axisWallChart A h v) t₀ ∧
        R v ∈ mainWallChartDomain k ∧
        axisWallChart B k (R v) = normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v))) ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
        Real.exp (∫ u in t₀..t,
          normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
            mainWallChartDensity h y ∧
      (∀ᶠ z : SectionCoordinates × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
        (B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ↔
          τ (axisWallChart A h z.1) = z.2)) := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcF⟩ := exists_normalized_axisWall_event B ht hk hlevel hp
  let F := fun x => normalizedMaxCurve x t₀ (τ x)
  let R := fun v => axisWallCoordinates B (F (axisWallChart A h v))
  have hF : F (axisWallChart A h y) = normalizedMaxCurve (axisWallChart A h y) t₀ t := by
    simp only [F, hτ]
  have hphysical := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical
    (axisWallChart_positive A hh y) (axisWallChart_constraint A hy) ht
  have hpos : positiveWalls (F (axisWallChart A h y)) := by rw [hF]; exact hphysical.1
  have hcC := contDiffAt_axisWallChart A hy (1 : WithTop ℕ∞)
  have hcFC : ContDiffAt ℝ 1 (fun v => F (axisWallChart A h v)) y := hcF.comp y hcC
  have hcR : ContDiffAt ℝ 1 R y := by
    convert! (contDiffAt_axisWallCoordinates B hpos 1).comp y hcFC using 1
  have hneg : ∀ᶠ v in 𝓝 y, B.map (F (axisWallChart A h v)) 0 < 0 := by
    have hc : ContinuousAt (fun v => B.map (F (axisWallChart A h v)) 0) y :=
      (continuous_apply (0 : Fin 5)).continuousAt.comp (B.map.continuous.continuousAt.comp hcFC.continuousAt)
    exact hc.eventually_lt continuousAt_const (by rw [hF]; exact hp)
  have hlocal : ∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
      τ (axisWallChart A h v) ∈ normalizedMaxDomain (axisWallChart A h v) t₀ ∧
      R v ∈ mainWallChartDomain k ∧ axisWallChart B k (R v) = F (axisWallChart A h v) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy,
      hcC.continuousAt.eventually hhit, hneg] with v hv he hn
    have hphys := (maximalNormalizedSolution (axisWallChart A h v) t₀).physical
      (axisWallChart_positive A hh v) (axisWallChart_constraint A hv) he.1
    exact ⟨hv, he.1, axisWallChart_coordinates B hphys.1 hphys.2 hn he.2⟩
  have heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y] (fun v => F (axisWallChart A h v)) :=
    hlocal.mono (fun _ hv => hv.2.2.2)
  refine ⟨τ, R, hτ, hcτ, hcR, ?_, hlocal, ?_, ?_, ?_⟩
  · exact congrArg (axisWallCoordinates B) hF
  · exact axisWall_coordinate_det_ne_zero A B hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
  · have H := axisWall_coordinate_jacobian A B hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
    simpa only [hτ] using H
  · have hc : ContinuousAt (fun z : SectionCoordinates × ℝ => (axisWallChart A h z.1, z.2)) (y, t) := by
      convert! ((contDiffAt_axisWallChart A hy 1).continuousAt.comp
        (continuousAt_fst (p := (y, t)))).prodMk continuousAt_snd using 1
    exact hc.eventually huniq

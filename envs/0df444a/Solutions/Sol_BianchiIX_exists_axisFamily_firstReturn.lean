-- Prove2me | solution 1 for BianchiIX.exists_axisFamily_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:37:42.449862+00:00
-- url     : https://prove2.me/submissions/c7b3d2f6-8406-4348-916b-f5237c4bf4cf

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Theorems.Thm_BianchiIX_AxisWallAtlasFamily_measure_image_of_firstPieces
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_NormalizedSymmetry_sectionFlux
import Theorems.Thm_BianchiIX_axisFamily_firstReturn_pair_injective
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_axisWall_coordinate_event
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_hasFDerivAt_normalizedMaxCurve
import Theorems.Thm_BianchiIX_mainWallChart_signed_flux
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
import Theorems.Thm_BianchiIX_normalizedSectionFlux_add_flow
import Theorems.Thm_BianchiIX_normalizedSectionFlux_flow
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_eq_exp_integral
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_gt_one
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod

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

private theorem BianchiIX.continuousAt_mainWallChartDensity {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) : ContinuousAt (mainWallChartDensity h) y := by
  have hp : mainWallChart h y 0 ≠ 0 := ne_of_lt (mainWallChart_negative hy)
  have hH : 0 ≤ wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  have hc : Continuous (fun v : SectionCoordinates => mainWallChart h v 0) := by
    unfold mainWallChart mainWallRadicand curvature
    fun_prop
  have hcH : Continuous (fun v : SectionCoordinates =>
      wallAmplitude h (Real.exp (-v 1)) (Real.exp (-v 2))) := by
    unfold wallAmplitude
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp (by fun_prop)
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
  exact (((hc.continuousAt.pow 2).add ((continuous_apply (0 : Fin 3)).continuousAt.pow 2)).sub
    (continuousAt_const.mul hc.continuousAt)).div
      (continuousAt_const.mul hc.continuousAt.abs) (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hp))
    |>.div (continuousAt_const.add (continuousAt_const.mul hcH.continuousAt)) (by linarith)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChartFrame_tangent (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (i : Fin 3) :
    normalizedConstraintDifferential (axisWallChart A h y) (axisWallChartFrame A h y i) = 0 :=
  congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1))
    (axisWallChartDifferential_tangent A hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.axisWallChart_flux (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    |normalizedSectionFlux (axisWallChart A h y) (axisWallChartFrame A h y)| = mainWallChartDensity h y := by
  rw [axisWallChart_signed_flux A hh hy, abs_neg, abs_of_pos (mainWallChartDensity_pos hh hy)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.eventually_arrival {y : SectionCoordinates} (hy : y ∈ P.source) :
    (fun v => axisWallChart B k (P.map v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (P.time (axisWallChart A h v))) := by
  filter_upwards [P.isOpen_source.mem_nhds hy] with v hv
  exact P.arrival v hv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.density_jacobian (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    mainWallChartDensity k (P.map y) * |(fderiv ℝ P.map y).det| =
      Real.exp (∫ u in t₀..P.time (axisWallChart A h y),
        normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
          mainWallChartDensity h y :=
  axisWall_coordinate_jacobian A B hh hk (P.source_chart hy) (P.target_chart hy) (P.time_mem y hy)
    ((P.time_regular y hy).differentiableAt (by norm_num))
    ((P.map_regular y hy).differentiableAt (by norm_num)) (P.eventually_arrival hy)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.jacobian_eq_exp (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    P.jacobian y = Real.exp (∫ u in t₀..P.time (axisWallChart A h y),
      normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) := by
  rw [jacobian, P.density_jacobian hh hk hy,
    mul_div_cancel_right₀ _ (ne_of_gt (mainWallChartDensity_pos hh (P.source_chart hy)))]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.jacobian_gt_one (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates}
    (hy : y ∈ P.source) (ht : t₀ < P.time (axisWallChart A h y)) : 1 < P.jacobian y := by
  rw [P.jacobian_eq_exp hh hk hy,
    ← normalizedVolumeJacobian_eq_exp_integral (axisWallChart_positive A hh y)
      (axisWallChart_constraint A (P.source_chart hy)) (P.time_mem y hy)]
  exact normalizedVolumeJacobian_gt_one (axisWallChart_positive A hh y)
    (axisWallChart_constraint A (P.source_chart hy)) ht

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

private theorem BianchiIX.AxisWallArrival.continuousOn_jacobian (hh : 0 < h) (hk : 0 < k) : ContinuousOn P.jacobian P.source := by
  have hcR : ContinuousOn P.map P.source := fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt
  have hcD : ContinuousOn (fderiv ℝ P.map) P.source :=
    (show ContDiffOn ℝ 1 P.map P.source from
      fun y hy => (P.map_regular y hy).contDiffWithinAt).continuousOn_fderiv_of_isOpen P.isOpen_source le_rfl
  have hcρ : ContinuousOn (fun y => mainWallChartDensity k (P.map y)) P.source :=
    fun y hy => (continuousAt_mainWallChartDensity hk (P.target_chart hy)).comp_continuousWithinAt
      (hcR y hy)
  exact (hcρ.mul ((ContinuousLinearMap.continuous_det.comp_continuousOn hcD).abs)).div
    (fun y hy => (continuousAt_mainWallChartDensity hh (P.source_chart hy)).continuousWithinAt)
    (fun y hy => ne_of_gt (mainWallChartDensity_pos hh (P.source_chart hy)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.lintegral_axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) (f : ι × SectionCoordinates → ℝ≥0∞) :
    (∫⁻ z, f z ∂axisFamilyMeasure k) = ∑' i, ∫⁻ y, f (i, y) ∂mainWallMeasure (k i) := by
  rw [axisFamilyMeasure, lintegral_sum_measure]
  exact tsum_congr (fun i => (measurableEmbedding_prodMk_left i).lintegral_map f)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.setLIntegral_axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) {S : Set (ι × SectionCoordinates)} (hS : MeasurableSet S)
    (f : ι × SectionCoordinates → ℝ≥0∞) :
    (∫⁻ z in S, f z ∂axisFamilyMeasure k) =
      ∑' i, ∫⁻ y in Prod.mk i ⁻¹' S, f (i, y) ∂mainWallMeasure (k i) := by
  rw [← lintegral_indicator hS, lintegral_axisFamilyMeasure]
  apply tsum_congr
  intro i
  rw [← lintegral_indicator (hS.preimage measurable_prodMk_left)]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.axisFamily_measure_image_of_fibers {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (k : ι → ℝ)
    {R : ι × SectionCoordinates → ι × SectionCoordinates} {j : ι × SectionCoordinates → ℝ≥0∞}
    {D S : Set (ι × SectionCoordinates)} (hinj : InjOn R D)
    (hlocal : ∀ i, ∀ T : Set SectionCoordinates, MeasurableSet T → T ⊆ Prod.mk i ⁻¹' D →
      MeasurableSet ((fun y => R (i, y)) '' T) ∧
        axisFamilyMeasure k ((fun y => R (i, y)) '' T) = ∫⁻ y in T, j (i, y) ∂mainWallMeasure (k i))
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ z in S, j z ∂axisFamilyMeasure k := by
  let Q (i : ι) := (fun y => R (i, y)) '' (Prod.mk i ⁻¹' S)
  have hQ (i : ι) := hlocal i (Prod.mk i ⁻¹' S) (hS.preimage measurable_prodMk_left)
    (fun _ hy => hSD hy)
  have hdisjoint : Pairwise (fun i l => Disjoint (Q i) (Q l)) := by
    intro i l hil
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact hil (congrArg Prod.fst (hinj (hSD hx) (hSD hy) heq.symm))
  have hdecomp : R '' S = ⋃ i, Q i := by
    ext z
    constructor
    · rintro ⟨⟨i, y⟩, hy, rfl⟩
      exact mem_iUnion.mpr ⟨i, y, hy, rfl⟩
    · intro hz
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hz
      exact ⟨(i, y), hy, rfl⟩
  refine ⟨hdecomp ▸ MeasurableSet.iUnion (fun i => (hQ i).1), ?_⟩
  rw [hdecomp, measure_iUnion hdisjoint (fun i => (hQ i).1), setLIntegral_axisFamilyMeasure k hS j]
  exact tsum_congr (fun i => (hQ i).2)

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

private theorem BianchiIX.AxisWallArrival.delay_lt_top_iff (E : Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    P.delay E I y < ∞ ↔ y ∈ P.eligible E I := by
  classical
  by_cases hy : y ∈ P.eligible E I <;> simp [delay, hy]

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
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstDelay_lt_top_iff (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) :
    C.firstDelay E I y < ∞ ↔ y ∈ axisFamilyHittingDomain A B h k t₀ E I := by
  rw [C.hittingDomain_eq_iUnion E I]
  simp only [firstDelay, iInf_lt_iff, AxisWallArrival.delay_lt_top_iff, mem_iUnion]

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

private theorem BianchiIX.AxisWallAtlasFamily.exists_firstDelay_branch [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hy : y ∈ axisFamilyHittingDomain A B h k t₀ E I) :
    ∃ i n, y ∈ ((C i).branch n).eligible (E i) I ∧
      ((C i).branch n).delay (E i) I y = C.firstDelay E I y ∧
      IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (((C i).branch n).coordinateTime y) := by
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hy
  obtain ⟨hfirst, i, n, hyn, hn⟩ := C.firstDelay_of_isLeast ht
  refine ⟨i, n, hyn, ?_, ?_⟩
  · rw [((C i).branch n).delay_of_mem hyn, hn, hfirst]
  · rwa [hn]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.axisFamily_firstReturn_injOn {ι : Type*} (B : ι → NormalizedSymmetry)
    {k : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    {R : ι × SectionCoordinates → ι × SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hfirst : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t) :
    InjOn R (axisFamilyReturnDomain B k t₀ E) := by
  intro x hx y hy heq
  obtain ⟨s, hs, hRx⟩ := hfirst x hx
  obtain ⟨t, ht, hRy⟩ := hfirst y hy
  exact axisFamily_firstReturn_pair_injective B hk hcharts hx.1 hy.1 hs ht
    (hRx.symm.trans ((congrArg (axisFamilyChart B k) heq).trans hRy))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.measurableSet_firstPiece {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) (q : ι × ℕ) :
    MeasurableSet (C.firstPiece E I q) := by
  have heq (r : ι × ℕ) : MeasurableSet {y |
      ((C r.1).branch r.2).delay (E r.1) I y = C.firstDelay E I y} :=
    measurableSet_eq_fun (((C r.1).branch r.2).measurable_delay (hE r.1) hI) (C.measurable_firstDelay hE hI)
  have hprev : MeasurableSet {y | ∀ r : ι × ℕ, Encodable.encode r < Encodable.encode q →
      ((C r.1).branch r.2).delay (E r.1) I y ≠ C.firstDelay E I y} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun r => MeasurableSet.iInter (fun _ => (heq r).compl))
  exact (((C q.1).branch q.2).measurableSet_eligible (hE q.1) hI).inter ((heq q).inter hprev)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstPiece_pairwiseDisjoint (E : ι → Set SectionCoordinates) (I : Set ℝ) :
    Pairwise (fun q r => Disjoint (C.firstPiece E I q) (C.firstPiece E I r)) := by
  intro q r hqr
  rw [disjoint_left]
  intro y hyq hyr
  have hcode : Encodable.encode q ≠ Encodable.encode r := fun heq => hqr (Encodable.encode_injective heq)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hyr.2.2 q hlt hyq.2.1
  · exact hyq.2.2 r hgt hyr.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.hittingDomain_eq_firstPieces [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i) :
    axisFamilyHittingDomain A B h k t₀ E I = ⋃ q, C.firstPiece E I q := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨i, n, _, hn, _⟩ := C.exists_firstDelay_branch hh hk hε hI hbound hy
    have hex : ∃ m : ℕ, ∃ q : ι × ℕ, Encodable.encode q = m ∧
        ((C q.1).branch q.2).delay (E q.1) I y = C.firstDelay E I y :=
      ⟨Encodable.encode (i, n), (i, n), rfl, hn⟩
    obtain ⟨q, hq, heq⟩ := Nat.find_spec hex
    have heligible : y ∈ ((C q.1).branch q.2).eligible (E q.1) I :=
      (((C q.1).branch q.2).delay_lt_top_iff (E q.1) I y).mp
        (heq ▸ (C.firstDelay_lt_top_iff E I y).mpr hy)
    refine mem_iUnion.mpr ⟨q, heligible, heq, fun r hr he => ?_⟩
    exact Nat.find_min hex (hq ▸ hr) ⟨r, rfl, he⟩
  · intro hy
    obtain ⟨q, hq⟩ := mem_iUnion.mp hy
    apply (C.firstDelay_lt_top_iff E I y).mp
    rw [← hq.2.1]
    exact (((C q.1).branch q.2).delay_lt_top_iff (E q.1) I y).mpr hq.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstPiece_isLeast [Finite ι] {ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    {q : ι × ℕ} {y : SectionCoordinates} (hy : y ∈ C.firstPiece E I q) :
    IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) (((C q.1).branch q.2).coordinateTime y) := by
  have hdomain : y ∈ axisFamilyHittingDomain A B h k t₀ E I := by
    rw [C.hittingDomain_eq_firstPieces hh hk hε hI hbound]
    exact mem_iUnion.mpr ⟨q, hy⟩
  obtain ⟨t, ht⟩ := exists_axisFamily_first_time A B hh hk hε hI hbound hdomain
  have H : ENNReal.ofReal (((C q.1).branch q.2).coordinateTime y - t₀) = ENNReal.ofReal (t - t₀) :=
    (((C q.1).branch q.2).delay_of_mem hy.1).symm.trans (hy.2.1.trans (C.firstDelay_of_isLeast ht).1)
  have heq := (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (hI hy.1.2.1))
    (sub_nonneg.mpr (hI ht.1.1))).mp H
  have htime : ((C q.1).branch q.2).coordinateTime y = t := sub_left_injective heq
  rwa [htime]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.exists_measurable_firstPiece_map [Nonempty ι] [MeasurableSpace ι]
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    ∃ R : SectionCoordinates → ι × SectionCoordinates, Measurable R ∧
      ∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q) := by
  classical
  let g (q : ι × ℕ) : SectionCoordinates → ι × SectionCoordinates := fun y =>
    (q.1, ((C q.1).branch q.2).source.piecewise ((C q.1).branch q.2).map (fun _ => 0) y)
  have hg (q : ι × ℕ) : Measurable (g q) := by
    have hm : Measurable (((C q.1).branch q.2).source.piecewise
        ((C q.1).branch q.2).map (fun _ => 0)) :=
      (show ContinuousOn ((C q.1).branch q.2).map ((C q.1).branch q.2).source from
      fun y hy => (((C q.1).branch q.2).map_regular y hy).continuousAt.continuousWithinAt).measurable_piecewise
        continuousOn_const ((C q.1).branch q.2).isOpen_source.measurableSet
    exact measurable_const.prodMk hm
  obtain ⟨R, hR, hpieces⟩ := exists_measurable_piecewise (C.firstPiece E I)
    (C.measurableSet_firstPiece hE hI) g hg (fun q r hqr y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint E I hqr)) hy.1 hy.2).elim)
  refine ⟨R, hR, fun q y hy => ?_⟩
  rw [hpieces q hy]
  exact congrArg (fun z => (q.1, z)) (piecewise_eq_of_mem _ _ _ hy.1.1)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_axisFamily_firstMap {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι] [MeasurableSpace ι]
    (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry) {h t₀ : ℝ} {k ε : ι → ℝ}
    {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i) (hI : I ⊆ Ici t₀)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hImeas : MeasurableSet I) :
    ∃ (C : AxisWallAtlasFamily A B h k t₀) (R : SectionCoordinates → ι × SectionCoordinates),
      Measurable R ∧
      (∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q)) ∧
      axisFamilyHittingDomain A B h k t₀ E I = ⋃ q, C.firstPiece E I q ∧
      ∀ y ∈ axisFamilyHittingDomain A B h k t₀ E I, ∃ t,
        IsLeast (axisFamilyHittingTimes A B h k t₀ E I y) t ∧
        (y, t) ∈ axisWallArrivalRelation A (B (R y).1) h (k (R y).1) t₀ ∧
        (R y).2 = axisWallCoordinates (B (R y).1) (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
        (R y).2 ∈ E (R y).1 := by
  obtain ⟨C⟩ := exists_axisWallAtlasFamily A B (t₀ := t₀) hh hk
  obtain ⟨R, hR, hpieces⟩ := C.exists_measurable_firstPiece_map hE hImeas
  have hcover := C.hittingDomain_eq_firstPieces hh hk hε hI hbound
  refine ⟨C, R, hR, hpieces, hcover, fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover ▸ hy)
  refine ⟨((C q.1).branch q.2).coordinateTime y, C.firstPiece_isLeast hh hk hε hI hbound hq, ?_⟩
  rw [hpieces q hq]
  exact ⟨((C q.1).branch q.2).mem_relation hq.1.1,
    ((C q.1).branch q.2).map_eq_coordinates hq.1.1, hq.1.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_axisFamily_firstReturnMap {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (C : ∀ i, AxisWallAtlasFamily (B i) B (k i) k t₀)
      (R : ι × SectionCoordinates → ι × SectionCoordinates),
      Measurable R ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ i q, EqOn (fun y => R (i, y))
        (fun y => (q.1, (((C i) q.1).branch q.2).map y)) ((C i).firstPiece E (Ioi t₀) q)) ∧
      (∀ i, axisFamilyHittingDomain (B i) B (k i) k t₀ E (Ioi t₀) =
        ⋃ q, (C i).firstPiece E (Ioi t₀) q) ∧
      ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E := by
  classical
  have hlocal (i : ι) := exists_axisFamily_firstMap (B i) B (t₀ := t₀) (hk i) hk hε
    (show Ioi t₀ ⊆ Ici t₀ from fun x hx => show t₀ ≤ x from le_of_lt hx) hbound hE measurableSet_Ioi
  choose C r hr hpieces hcover hfirst using hlocal
  let R : ι × SectionCoordinates → ι × SectionCoordinates := fun z => r z.1 z.2
  have hR : Measurable R := measurable_from_prod_countable_right hr
  have hspec : ∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
      IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
      axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
      R z ∈ axisFamilySection E := by
    intro z hz
    obtain ⟨t, ht, hrel, hcoord, htarget⟩ := hfirst z.1 z.2 hz.2
    refine ⟨t, ht, ?_, htarget⟩
    change axisWallChart (B (r z.1 z.2).1) (k (r z.1 z.2).1) (r z.1 z.2).2 = _
    rw [hcoord]
    exact axisWallArrivalRelation_chart (B z.1) (B (r z.1 z.2).1) (hk z.1) hrel
  exact ⟨C, R, hR, axisFamily_firstReturn_injOn B hk hcharts
    (fun z hz => let ⟨t, ht, hstate, _⟩ := hspec z hz; ⟨t, ht, hstate⟩), hpieces, hcover, hspec⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry} {h t₀ : ℝ} {k : ι → ℝ}
  (C : AxisWallAtlasFamily A B h k t₀)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private theorem BianchiIX.AxisWallAtlasFamily.exists_measurable_firstPiece_jacobian {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : 0 < h) (hk : ∀ i, 0 < k i) (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) :
    ∃ j : SectionCoordinates → ℝ≥0∞, Measurable j ∧
      ∀ q : ι × ℕ, EqOn j (fun y => ENNReal.ofReal (((C q.1).branch q.2).jacobian y)) (C.firstPiece E I q) := by
  classical
  let g (q : ι × ℕ) : SectionCoordinates → ℝ :=
    ((C q.1).branch q.2).source.piecewise ((C q.1).branch q.2).jacobian (fun _ => 0)
  have hg (q : ι × ℕ) : Measurable (g q) :=
    (((C q.1).branch q.2).continuousOn_jacobian hh (hk q.1)).measurable_piecewise
      continuousOn_const ((C q.1).branch q.2).isOpen_source.measurableSet
  obtain ⟨j, hj, hpieces⟩ := exists_measurable_piecewise (C.firstPiece E I)
    (C.measurableSet_firstPiece hE hI) (fun q y => ENNReal.ofReal (g q y))
    (fun q => (hg q).ennreal_ofReal) (fun q r hqr y hy =>
      ((disjoint_left.mp (C.firstPiece_pairwiseDisjoint E I hqr)) hy.1 hy.2).elim)
  refine ⟨j, hj, fun q y hy => ?_⟩
  rw [hpieces q hy]
  change ENNReal.ofReal (g q y) = ENNReal.ofReal (((C q.1).branch q.2).jacobian y)
  rw [show g q y = ((C q.1).branch q.2).jacobian y from piecewise_eq_of_mem _ _ _ hy.1.1]

end
end

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal



/-- The actual first return on an injectively represented finite section family has exact global transport. -/
theorem solution {ι : Type*} [Finite ι] [Encodable ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (B : ι → NormalizedSymmetry)
    {k ε : ι → ℝ} {t₀ : ℝ} {E : ι → Set SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hε : ∀ i, 0 < ε i)
    (hbound : ∀ i, ∀ z ∈ E i, mainWallChart (k i) z 0 ≤ -ε i)
    (hE : ∀ i, MeasurableSet (E i)) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E)) :
    ∃ (R : ι × SectionCoordinates → ι × SectionCoordinates) (j : ι × SectionCoordinates → ℝ≥0∞),
      Measurable R ∧ Measurable j ∧ InjOn R (axisFamilyReturnDomain B k t₀ E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, ∃ t,
        IsLeast (axisFamilyReturnTimes B k t₀ E z) t ∧
        axisFamilyChart B k (R z) = normalizedMaxCurve (axisFamilyChart B k z) t₀ t ∧
        R z ∈ axisFamilySection E) ∧
      (∀ z ∈ axisFamilyReturnDomain B k t₀ E, 1 < j z ∧ j z < ∞) ∧
      ∀ S, MeasurableSet S → S ⊆ axisFamilyReturnDomain B k t₀ E →
        MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ z in S, j z ∂axisFamilyMeasure k := by
  classical
  obtain ⟨C, R, hR, hinj, hpiecesR, hcover, hfirst⟩ :=
    exists_axisFamily_firstReturnMap B (t₀ := t₀) hk hε hbound hE hcharts
  have hjlocal (i : ι) := (C i).exists_measurable_firstPiece_jacobian
    (I := Ioi t₀) (hk i) hk hE measurableSet_Ioi
  choose J hJ hpiecesJ using hjlocal
  let j : ι × SectionCoordinates → ℝ≥0∞ := fun z => J z.1 z.2
  have hj : Measurable j := measurable_from_prod_countable_right hJ
  have hcoverD (i : ι) : Prod.mk i ⁻¹' axisFamilyReturnDomain B k t₀ E ⊆
      ⋃ q, (C i).firstPiece E (Ioi t₀) q := fun _ hy => hcover i ▸ hy.2
  refine ⟨R, j, hR, hj, hinj, hfirst, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcoverD z.1 hz)
    change 1 < J z.1 z.2 ∧ J z.1 z.2 < ∞
    rw [hpiecesJ z.1 q hq]
    exact ⟨ENNReal.one_lt_ofReal.mpr ((((C z.1) q.1).branch q.2).jacobian_gt_one
      (hk z.1) (hk q.1) hq.1.1 hq.1.2.1), ENNReal.ofReal_lt_top⟩
  · intro S hS hSD
    apply axisFamily_measure_image_of_fibers k hinj _ hS hSD
    intro i T hT hTD
    have hinji : InjOn (fun y => R (i, y)) (Prod.mk i ⁻¹' axisFamilyReturnDomain B k t₀ E) := by
      intro x hx y hy heq
      exact congrArg Prod.snd (hinj hx hy heq)
    exact (C i).measure_image_of_firstPieces (hk i) hE measurableSet_Ioi (hcoverD i) hinji
      (hpiecesR i) (hpiecesJ i) hT hTD

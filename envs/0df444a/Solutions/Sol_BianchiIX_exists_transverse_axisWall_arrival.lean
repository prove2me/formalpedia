-- Prove2me | solution 1 for BianchiIX.exists_transverse_axisWall_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:35:16.14548+00:00
-- url     : https://prove2.me/submissions/0e5f331b-1a12-4c36-ae80-ace27c03b363

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_hasFDerivAt_normalizedMaxCurve
import Theorems.Thm_BianchiIX_isOpen_positiveWalls
import Theorems.Thm_BianchiIX_normalizedSectionFlux_add_flow
import Theorems.Thm_BianchiIX_normalizedSectionFlux_flow
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_eq_exp_integral
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension

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


/-- Every actual wall hit from a transverse constraint chart has a nonsingular local arrival map. -/
theorem solution (A : NormalizedSymmetry)
    {C : SectionCoordinates → NormalizedState} {y : SectionCoordinates} {t₀ t h : ℝ}
    (hC : ContDiffAt ℝ 1 C y) (hp : positiveWalls (C y))
    (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ht : t ∈ normalizedMaxDomain (C y) t₀) (hh : 0 < h)
    (hlevel : A.map (normalizedMaxCurve (C y) t₀ t) 2 = h)
    (hneg : A.map (normalizedMaxCurve (C y) t₀ t) 0 < 0) :
    ∃ R : SectionCoordinates → SectionCoordinates, ContDiffAt ℝ 1 R y ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      ∀ᶠ p : SectionCoordinates × ℝ in 𝓝 (y, t),
        A.map (normalizedMaxCurve (C p.1) t₀ p.2) 2 = h →
          R p.1 = axisWallCoordinates A (normalizedMaxCurve (C p.1) t₀ p.2) := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcMap⟩ :=
    exists_normalized_axisWall_event A ht hh hlevel hneg
  let F := fun v => normalizedMaxCurve (C v) t₀ (τ (C v))
  let R := fun v => axisWallCoordinates A (F v)
  have hF : ContDiffAt ℝ 1 F y := hcMap.comp y hC
  have hFy : F y = normalizedMaxCurve (C y) t₀ t := by simp only [F, hτ]
  have hpF : positiveWalls (F y) := by
    rw [hFy]
    exact ((maximalNormalizedSolution (C y) t₀).physical hp hc.self_of_nhds ht).1
  have hR : ContDiffAt ℝ 1 R y := (contDiffAt_axisWallCoordinates A hpF 1).comp y hF
  have hpos : ∀ᶠ v in 𝓝 y, positiveWalls (F v) :=
    hF.continuousAt.eventually (isOpen_positiveWalls.mem_nhds hpF)
  have hnegative : ∀ᶠ v in 𝓝 y, A.map (F v) 0 < 0 := by
    have H : ContinuousAt (fun v => A.map (F v) 0) y := by fun_prop
    exact H.eventually_lt continuousAt_const (by rw [hFy]; exact hneg)
  have hlocal : ∀ᶠ v in 𝓝 y, R v ∈ mainWallChartDomain h ∧ axisWallChart A h (R v) = F v := by
    filter_upwards [hc, hC.continuousAt.eventually hhit, hpos, hnegative] with v hcv htv hpv hnv
    exact axisWallChart_coordinates A hpv ((normalizedMaxCurve_constraint htv.1).trans hcv) hnv htv.2
  have hdet : (fderiv ℝ R y).det ≠ 0 :=
    normalized_chart_arrival_det_ne_zero (hC.differentiableAt (by norm_num))
      ((contDiffAt_axisWallChart A hlocal.self_of_nhds.1 1).differentiableAt (by norm_num))
      (hR.differentiableAt (by norm_num)) (hcτ.differentiableAt (by norm_num)) hp hc
      (by rw [hτ]; exact ht) hflux (hlocal.mono fun _ hv => hv.2)
  refine ⟨R, hR, hdet, ?_⟩
  have hpair : Tendsto (fun p : SectionCoordinates × ℝ => (C p.1, p.2))
      (𝓝 (y, t)) (𝓝 (C y, t)) :=
    (hC.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [hpair.eventually huniq] with p hp hlevel'
  have htime : τ (C p.1) = p.2 := hp.2.mp hlevel'
  simp only [R, F, htime]

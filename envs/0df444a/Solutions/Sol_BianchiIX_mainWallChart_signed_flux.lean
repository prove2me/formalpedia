-- Prove2me | solution 1 for BianchiIX.mainWallChart_signed_flux
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:34:49.267692+00:00
-- url     : https://prove2.me/submissions/f71fc701-1324-4bcc-904c-f6c1f2237fe1

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_hasDerivAt_stateConstraint
import Theorems.Thm_BianchiIX_normalizedConstraintVolume_normal
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

noncomputable section
open BianchiIX

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

private theorem BianchiIX.normalizedConstraintDifferential_field (x : NormalizedState) :
    normalizedConstraintDifferential x (normalizedField x) = 0 := by
  have hα := hasDerivAt_normalizedMaxCurve (initial_mem_normalizedMaxDomain x 0)
  have H := (hasFDerivAt_stateConstraint (normalizedMaxCurve x 0 0)).comp_hasDerivAt 0 hα
  simpa only [normalizedMaxCurve_initial] using H.unique (hasDerivAt_stateConstraint hα)

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

private theorem BianchiIX.mainWallChartDifferential_tangent {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    (normalizedConstraintDifferential (mainWallChart h y)).comp (mainWallChartDifferential h y) = 0 := by
  have H := (hasFDerivAt_stateConstraint (mainWallChart h y)).comp y (hasFDerivAt_mainWallChart hy)
  have heq : (fun _ : SectionCoordinates => (1 : ℝ)) =ᶠ[𝓝 y]
      (fun z => stateConstraint (mainWallChart h z)) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy] with z hz
    exact (mainWallChart_constraint hz).symm
  exact (H.congr_of_eventuallyEq heq).unique (hasFDerivAt_const 1 y)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChartDifferential_components {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (v : SectionCoordinates) :
    mainWallChartDifferential h y v 1 = v 0 ∧
      mainWallChartDifferential h y v 2 = 0 ∧
      mainWallChartDifferential h y v 3 = -Real.exp (-y 1) * v 1 ∧
      mainWallChartDifferential h y v 4 = -Real.exp (-y 2) * v 2 := by
  have H (i : Fin 5) := (hasFDerivAt_apply (𝕜 := ℝ) i (mainWallChart h y)).comp y
    (hasFDerivAt_mainWallChart hy)
  have h₁ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 1).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) y))
  have h₂ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 2).unique (hasFDerivAt_const h y))
  have h₃ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 3).unique (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) y).neg.exp)
  have h₄ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 4).unique (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) y).neg.exp)
  exact ⟨h₁, h₂, by simpa using h₃, by simpa using h₄⟩

end
end

private theorem BianchiIX.normalizedConstraintDifferential_first (x : NormalizedState) :
    normalizedConstraintDifferential x (Pi.single 0 1) = 2 * x 0 := by
  have H := (hasFDerivAt_stateConstraint (Function.update x 0 (x 0))).comp_hasDerivAt (x 0)
    (hasDerivAt_update x 0 (x 0))
  simp only [Function.update_eq_self] at H
  apply H.unique
  simpa [Function.comp_def, stateConstraint, constraint, shearSq] using
    (((hasDerivAt_id (x 0)).pow 2).add_const (x 1 ^ 2)).add_const (curvature (x 2) (x 3) (x 4))

private theorem BianchiIX.mainWall_volume_determinant (a b c u v w : ℝ) (F : NormalizedState) :
    normalizedAmbientVolume ![![a, 0, 0, 0, 0], F, ![u, 1, 0, 0, 0],
      ![v, 0, 0, -b, 0], ![w, 0, 0, 0, -c]] = -a * F 2 * b * c := by
  rw [normalizedAmbientVolume, Pi.basisFun_det_apply]
  have hm : (Matrix.of ![![a, 0, 0, 0, 0], F, ![u, 1, 0, 0, 0],
      ![v, 0, 0, -b, 0], ![w, 0, 0, 0, -c]]).submatrix Fin.succ Fin.succ =
      !![F 1, F 2, F 3, F 4; 1, 0, 0, 0; 0, 0, -b, 0; 0, 0, 0, -c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ]
  rw [hm]
  have hn : (!![F 1, F 2, F 3, F 4; 1, 0, 0, 0; 0, 0, -b, 0; 0, 0, 0, -c]).submatrix
      (1 : Fin 4).succAbove Fin.succ = !![F 2, F 3, F 4; 0, -b, 0; 0, 0, -c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row _ 1]
  norm_num [Fin.sum_univ_succ]
  rw [hn]
  rw [Matrix.det_fin_three]
  simp
  ring

private theorem BianchiIX.mainWallChartFrame_tangent {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (i : Fin 3) :
    normalizedConstraintDifferential (mainWallChart h y) (mainWallChartFrame h y i) = 0 :=
  congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1)) (mainWallChartDifferential_tangent hy)


theorem solution {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    normalizedSectionFlux (mainWallChart h y) (mainWallChartFrame h y) = -mainWallChartDensity h y := by
  let x := mainWallChart h y
  let V := mainWallChartFrame h y
  let X : NormalizedState := (2 * x 0)⁻¹ • Pi.single 0 1
  have hp : x 0 < 0 := mainWallChart_negative hy
  have hX : normalizedConstraintDifferential x X = 1 := by
    rw [map_smul, normalizedConstraintDifferential_first]
    exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (ne_of_lt hp))
  have htan : ∀ i : Fin 4, normalizedConstraintDifferential x ((Fin.cons (normalizedField x) V :
      Fin 4 → NormalizedState) i) = 0 := by
    intro i
    exact Fin.cases (normalizedConstraintDifferential_field x) (mainWallChartFrame_tangent hy) i
  change normalizedConstraintVolume x (Fin.cons (normalizedField x) V) = _
  rw [normalizedConstraintVolume_normal (mainWallChart_constraint hy) hX htan]
  have hcoords (i : Fin 3) := mainWallChartDifferential_components hy (Pi.single i 1)
  have hframe : Fin.cons X (Fin.cons (normalizedField x) V) =
      ![![(2 * x 0)⁻¹, 0, 0, 0, 0], normalizedField x, ![V 0 0, 1, 0, 0, 0],
        ![V 1 0, 0, 0, -Real.exp (-y 1), 0], ![V 2 0, 0, 0, 0, -Real.exp (-y 2)]] := by
    funext i
    fin_cases i
    · ext j
      fin_cases j <;> simp [X]
    · rfl
    · change V 0 = ![V 0 0, 1, 0, 0, 0]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 0).1
      · exact (hcoords 0).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 0).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 0).2.2.2
    · change V 1 = ![V 1 0, 0, 0, -Real.exp (-y 1), 0]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 1).1
      · exact (hcoords 1).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 1).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 1).2.2.2
    · change V 2 = ![V 2 0, 0, 0, 0, -Real.exp (-y 2)]
      ext j
      fin_cases j
      · rfl
      · simpa [V, mainWallChartFrame] using (hcoords 2).1
      · exact (hcoords 2).2.1
      · simpa [V, mainWallChartFrame] using (hcoords 2).2.2.1
      · simpa [V, mainWallChartFrame] using (hcoords 2).2.2.2
  rw [hframe, mainWall_volume_determinant]
  change -(2 * x 0)⁻¹ * (rateOne (x 0) (y 0) * h) * Real.exp (-y 1) * Real.exp (-y 2) /
    (h * Real.exp (-y 1) * Real.exp (-y 2) *
      (1 + 4 * wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)))) = _
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity
  rw [abs_of_neg hp]
  unfold rateOne
  field_simp [ne_of_lt hp, ne_of_gt hh, Real.exp_ne_zero]
  ring

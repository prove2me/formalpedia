-- Prove2me | solution 1 for BianchiIX.axisFamily_firstReturn_pair_injective
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:34:54.89793+00:00
-- url     : https://prove2.me/submissions/4baa373e-e143-4ad6-8f14-ae53f9f8de98

import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
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

noncomputable section
open BianchiIX
open Set MeasureTheory

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
open Set

private theorem BianchiIX.normalizedMaxCurve_eq_at_time_difference {x y : NormalizedState} {t₀ s t : ℝ}
    (hxpos : positiveWalls x) (hxcon : stateConstraint x = 1)
    (hypos : positiveWalls y) (hycon : stateConstraint y = 1)
    (hs : t₀ ≤ s) (hst : s ≤ t)
    (heq : normalizedMaxCurve x t₀ s = normalizedMaxCurve y t₀ t) :
    normalizedMaxCurve y t₀ (t₀ + (t - s)) = x := by
  have hu := normalizedMaxDomain_contains_Ici hypos hycon t₀
    (show t₀ ≤ t₀ + (t - s) by linarith)
  have ht := normalizedMaxDomain_contains_Ici hypos hycon t₀ (hs.trans hst)
  have hp := (maximalNormalizedSolution y t₀).physical hypos hycon hu
  apply normalizedMaxCurve_injOn t₀ s
    (normalizedMaxDomain_contains_Ici hp.1 hp.2 t₀ hs)
    (normalizedMaxDomain_contains_Ici hxpos hxcon t₀ hs)
  have H := normalizedMaxCurve_shift hu (show s + (t - s) ∈ normalizedMaxDomain y t₀ by
    simpa using ht)
  convert! H.trans (by simpa using heq.symm) using 1

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
open Set MeasureTheory

private theorem BianchiIX.axisFamilyHittingTimes_source {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
    {h t₀ t : ℝ} {k : ι → ℝ} {E : ι → Set SectionCoordinates} {I : Set ℝ} {y : SectionCoordinates}
    (ht : t ∈ axisFamilyHittingTimes A B h k t₀ E I y) : y ∈ mainWallChartDomain h := by
  obtain ⟨_, _, hrel, _⟩ := ht
  exact hrel.1

end
end


/-- Earliest returns cannot merge; injective physical charts remove any ambiguity of axis labels. -/
theorem solution {ι : Type*} (B : ι → NormalizedSymmetry)
    {k : ι → ℝ} {t₀ s t : ℝ} {E : ι → Set SectionCoordinates} {x y : ι × SectionCoordinates}
    (hk : ∀ i, 0 < k i) (hcharts : InjOn (axisFamilyChart B k) (axisFamilySection E))
    (hx : x ∈ axisFamilySection E) (hy : y ∈ axisFamilySection E)
    (hs : IsLeast (axisFamilyReturnTimes B k t₀ E x) s)
    (ht : IsLeast (axisFamilyReturnTimes B k t₀ E y) t)
    (heq : normalizedMaxCurve (axisFamilyChart B k x) t₀ s =
      normalizedMaxCurve (axisFamilyChart B k y) t₀ t) : x = y := by
  have hnot {u v : ι × SectionCoordinates} {a b : ℝ} (hu : u ∈ axisFamilySection E)
      (ha : IsLeast (axisFamilyReturnTimes B k t₀ E u) a)
      (hb : IsLeast (axisFamilyReturnTimes B k t₀ E v) b) (hab : a < b)
      (H : normalizedMaxCurve (axisFamilyChart B k u) t₀ a =
        normalizedMaxCurve (axisFamilyChart B k v) t₀ b) : False := by
    have huc := axisFamilyHittingTimes_source ha.1
    have hvc := axisFamilyHittingTimes_source hb.1
    have hz := normalizedMaxCurve_eq_at_time_difference
      (axisWallChart_positive (B u.1) (hk u.1) u.2) (axisWallChart_constraint (B u.1) huc)
      (axisWallChart_positive (B v.1) (hk v.1) v.2) (axisWallChart_constraint (B v.1) hvc)
      ha.1.1.le hab.le H
    have htime : t₀ + (b - a) ∈ axisFamilyReturnTimes B k t₀ E v := by
      refine ⟨by change t₀ < t₀ + (b - a); linarith, u.1, ⟨hvc, ?_, ?_, ?_⟩, ?_⟩
      · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B v.1) (hk v.1) v.2)
          (axisWallChart_constraint (B v.1) hvc) t₀ (show t₀ ≤ t₀ + (b - a) by linarith)
      · rw [hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
        rfl
      · rw [hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
        exact mainWallChart_negative huc
      · rw [hz, axisWallCoordinates_chart]
        exact hu
    have hmin := hb.2 htime
    have ha0 := ha.1.1
    change t₀ < a at ha0
    linarith
  have hst : s = t := by
    rcases lt_trichotomy s t with hlt | he | hgt
    · exact (hnot hx hs ht hlt heq).elim
    · exact he
    · exact (hnot hy ht hs hgt heq.symm).elim
  have hs0 : t₀ < s := hs.1.1
  apply hcharts hx hy
  apply normalizedMaxCurve_injOn t₀ s
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B x.1) (hk x.1) x.2)
      (axisWallChart_constraint (B x.1) (axisFamilyHittingTimes_source hs.1)) t₀ hs0.le
  · exact normalizedMaxDomain_contains_Ici (axisWallChart_positive (B y.1) (hk y.1) y.2)
      (axisWallChart_constraint (B y.1) (axisFamilyHittingTimes_source ht.1)) t₀ hs0.le
  · simpa [hst] using heq

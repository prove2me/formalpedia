-- Prove2me | solution 1 for BianchiIX.exists_smallAxis_borel_first_success
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:39:40.597544+00:00
-- url     : https://prove2.me/submissions/90d51e89-fb43-478e-b737-512b8f964aaf

import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_exists_axisFamily_firstReturn
import Theorems.Thm_BianchiIX_exists_axisWall_coordinate_event
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
import Theorems.Thm_BianchiIX_normalizedMaxDomain_rebase
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

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

private theorem BianchiIX.exists_least_of_finite_initial_intervals {S : Set ℝ} {a : ℝ}
    (hS : S ⊆ Ici a) (hne : S.Nonempty) (hfinite : ∀ b, (S ∩ Icc a b).Finite) :
    ∃ t, IsLeast S t := by
  obtain ⟨b, hb⟩ := hne
  obtain ⟨t, ht, hmin⟩ := Set.exists_min_image (S ∩ Icc a b) id (hfinite b) ⟨b, hb, hS hb, le_rfl⟩
  refine ⟨t, ht.1, fun u hu => ?_⟩
  by_cases hub : u ≤ b
  · exact hmin u ⟨hu, hS hu, hub⟩
  · exact ht.2.2.trans (le_of_not_ge hub)

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
open scoped ENNReal

private theorem BianchiIX.globalAxisWallHittingDomain_eq_image {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} (I : Set ℝ)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    globalAxisWallHittingDomain A h B I = ⋃ i, axisWallFlowMap (A i) (h i) ''
      {p | p.1 ∈ B i ∧ p ∈ axisWallFlowDomain (A i) (h i) ∧ -p.2 ∈ I} := by
  ext x
  constructor
  · rintro ⟨t, htI, ht, i, y, hy, heq⟩
    have H := normalizedMaxCurve_inverse ht
    rw [← heq] at H
    exact mem_iUnion.mpr ⟨i, (y, -t), ⟨hy, ⟨hchart i hy, H.1⟩, by simpa using htI⟩, H.2⟩
  · intro hx
    obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.mp hx
    have H := normalizedMaxCurve_inverse hp.2.1.2
    exact ⟨-p.2, hp.2.2, H.1, i, p.1, hp.1, H.2.symm⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_globalAxisWallHittingDomain {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    MeasurableSet (globalAxisWallHittingDomain A h B I) := by
  rw [globalAxisWallHittingDomain_eq_image A I hchart]
  apply MeasurableSet.iUnion
  intro i
  apply measurableSet_axisWallFlowMap_image (A i) (hh i)
  · exact (hB i |>.preimage measurable_fst).inter
      ((isOpen_axisWallFlowDomain (A i) (h i)).measurableSet.inter
        (hI.preimage measurable_snd.neg))
  · exact fun _ hp => hp.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.globalAxisWallFirstDelay_lt_iff {ι : Type*} (A : ι → NormalizedSymmetry)
    (h : ι → ℝ) (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) (r : ℝ≥0∞) :
    globalAxisWallFirstDelay A h B I x < r ↔
      x ∈ globalAxisWallHittingDomain A h B (I ∩ {t | ENNReal.ofReal t < r}) := by
  simp only [globalAxisWallFirstDelay, iInf_lt_iff, globalAxisWallHittingDomain,
    globalAxisWallHittingTimes, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
  constructor
  · rintro ⟨⟨t, htI, ht, hy⟩, hr⟩
    exact ⟨t, ⟨htI, hr⟩, ht, hy⟩
  · rintro ⟨t, ⟨htI, hr⟩, ht, hy⟩
    exact ⟨⟨t, htI, ht, hy⟩, hr⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_globalAxisWallFirstDelay {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstDelay A h B I) := by
  apply measurable_of_Iio
  intro r
  have heq : globalAxisWallFirstDelay A h B I ⁻¹' Iio r =
      globalAxisWallHittingDomain A h B (I ∩ {t | ENNReal.ofReal t < r}) := by
    ext x
    exact globalAxisWallFirstDelay_lt_iff A h B I x r
  rw [heq]
  exact measurableSet_globalAxisWallHittingDomain A hh hB
    (hI.inter (measurableSet_lt ENNReal.measurable_ofReal measurable_const)) hchart

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.finite_globalAxisWallHittingTimes {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} {T : ℝ} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i) :
    (globalAxisWallHittingTimes A h B I x ∩ Icc 0 T).Finite := by
  let α := fun i => normalizedMaxCurve ((A i).map x) 0
  have hderiv (i : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :=
    hasDerivAt_normalized_components (hasDerivAt_normalizedMaxCurve
      (normalizedMaxDomain_contains_Ici ((A i).positive x |>.mpr hp)
        ((A i).constraint x |>.trans hc) 0 ht.1))
  have hf (i : ι) : {t ∈ Icc 0 T | α i t 2 = h i ∧ α i t 0 ≤ -ε i}.Finite :=
    finite_negative_section_times isCompact_Icc
      (fun t ht => (hderiv i t ht).2.2.1.continuousAt.continuousWithinAt)
      (fun t ht => (hderiv i t ht).1.continuousAt.continuousWithinAt)
      (hh i) (hε i) (fun t ht => (hderiv i t ht).2.2.1)
  apply (Set.finite_iUnion hf).subset
  rintro t ⟨⟨_, ht, i, y, hy, heq⟩, htK⟩
  have he : α i t = mainWallChart (h i) y := by
    rw [show α i t = (A i).map (normalizedMaxCurve x 0 t) from (A i).maxCurve ht,
      ← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
  exact mem_iUnion.mpr ⟨i, htK, by rw [he]; rfl, by rw [he]; exact hbound i y hy⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.exists_globalAxisWall_first_time {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    ∃ t, IsLeast (globalAxisWallHittingTimes A h B I x) t :=
  exists_least_of_finite_initial_intervals (fun _ ht => hI ht.1) hx
    (fun _ => finite_globalAxisWallHittingTimes A hh hε hp hc hbound)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.globalAxisWallFirstDelay_of_isLeast {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState} {t : ℝ}
    (ht : IsLeast (globalAxisWallHittingTimes A h B I x) t) :
    globalAxisWallFirstDelay A h B I x = ENNReal.ofReal t := by
  unfold globalAxisWallFirstDelay
  apply le_antisymm
  · exact iInf_le (fun u : globalAxisWallHittingTimes A h B I x => ENNReal.ofReal u.val) ⟨t, ht.1⟩
  · exact le_iInf fun u => ENNReal.ofReal_le_ofReal (ht.2 u.property)

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

private theorem BianchiIX.measurable_normalizedMaxCurve (t₀ : ℝ) :
    Measurable (fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 t₀ p.2) := by
  classical
  have H := ContinuousOn.measurable_piecewise
    (s := normalizedFlowDomain t₀)
    (f := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 t₀ p.2)
    (fun p hp => (normalizedMaxCurve_regular hp).2.continuousAt.continuousWithinAt)
    continuous_fst.continuousOn (isOpen_normalizedFlowDomain t₀).measurableSet
  convert! H using 1
  funext p
  by_cases hp : p ∈ normalizedFlowDomain t₀
  · simp only [piecewise_eq_of_mem _ _ _ hp]
  · rw [piecewise_eq_of_notMem _ _ _ hp]
    exact dif_neg hp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_globalAxisWallFirstTime {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstTime A h B I) :=
  (measurable_globalAxisWallFirstDelay A hh hB hI hchart).ennreal_toReal

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_globalAxisWallFirstState {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    (hh : ∀ i, 0 < h i) (hB : ∀ i, MeasurableSet (B i)) (hI : MeasurableSet I)
    (hchart : ∀ i, B i ⊆ mainWallChartDomain (h i)) :
    Measurable (globalAxisWallFirstState A h B I) :=
  (measurable_normalizedMaxCurve 0).comp
    (measurable_id.prodMk (measurable_globalAxisWallFirstTime A hh hB hI hchart))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.globalAxisWallFirstTime_of_isLeast {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ} {x : NormalizedState} {t : ℝ}
    (hI : I ⊆ Ici 0) (ht : IsLeast (globalAxisWallHittingTimes A h B I x) t) :
    globalAxisWallFirstTime A h B I x = t := by
  rw [globalAxisWallFirstTime, globalAxisWallFirstDelay_of_isLeast A ht,
    ENNReal.toReal_ofReal (hI ht.1.1)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.globalAxisWallFirstTime_isLeast {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hbound : ∀ i, ∀ y ∈ B i, mainWallChart (h i) y 0 ≤ -ε i)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    IsLeast (globalAxisWallHittingTimes A h B I x) (globalAxisWallFirstTime A h B I x) := by
  obtain ⟨t, ht⟩ := exists_globalAxisWall_first_time A hh hε hp hc hI hbound hx
  rwa [globalAxisWallFirstTime_of_isLeast A hI ht]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.globalAxisWallFirstTime_small_target {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {B : ι → Set SectionCoordinates} {I : Set ℝ}
    {x : NormalizedState} (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i ≤ 1 / 8)
    (hp : positiveWalls x) (hc : stateConstraint x = 1) (hI : I ⊆ Ici 0)
    (hsmall : ∀ i, ∀ y ∈ B i, y ∈ mainWallChartDomain (h i) ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h i / 8 ∧ Real.exp (-y 2) ≤ h i / 8)
    (hx : x ∈ globalAxisWallHittingDomain A h B I) :
    IsLeast (globalAxisWallHittingTimes A h B I x) (globalAxisWallFirstTime A h B I x) := by
  apply globalAxisWallFirstTime_isLeast A hh (ε := fun _ => 15 / 16)
    (fun _ => by norm_num) hp hc hI _ hx
  intro i y hy
  exact mainWall_small_target_shear (hh i) (hh1 i) (hsmall i y hy).1
    (hsmall i y hy).2.1 (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2

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

private theorem BianchiIX.measurableSet_axisFamilySuccessTargets {ι : Type*} [MeasurableSpace ι]
    {E : ι → Set SectionCoordinates} {F : Set (ι × SectionCoordinates)}
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F) (i : ι) :
    MeasurableSet (axisFamilySuccessTargets E F i) :=
  (hE i).diff (hF.preimage (measurable_const.prodMk measurable_id))

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


/-- One Borel first-success pair works for every physical initial state that reaches the target. -/
theorem solution {h : ℝ} {E : Fin 3 → Set SectionCoordinates}
    {F : Set (Fin 3 × SectionCoordinates)} (hh : 0 < h) (hh1 : h ≤ 1 / 8)
    (hE : ∀ i, MeasurableSet (E i))
    (hsmall : ∀ i, ∀ y ∈ E i, y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
      Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8)
    (hF : MeasurableSet F) (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ∞) :
    ∃ τ : NormalizedState → ℝ, ∃ Y : NormalizedState → NormalizedState,
      Measurable τ ∧ Measurable Y ∧ (∀ x, Y x = normalizedMaxCurve x 0 (τ x)) ∧
      (∀ x, positiveWalls x → stateConstraint x = 1 →
        x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) →
        IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) x) (τ x) ∧
          ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x) ∧
      (∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
        z ∈ axisFamilyInfiniteReturns primaryAxisFrame (fun _ => h) 0 E →
          let x := axisFamilyChart primaryAxisFrame (fun _ => h) z
          IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) x) (τ x) ∧
            ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x) := by
  let B := axisFamilySuccessTargets E F
  let τ := globalAxisWallFirstTime primaryAxisFrame (fun _ => h) B (Ici 0)
  let Y := globalAxisWallFirstState primaryAxisFrame (fun _ => h) B (Ici 0)
  have hB := measurableSet_axisFamilySuccessTargets hE hF
  have hchart (i : Fin 3) : B i ⊆ mainWallChartDomain h := fun y hy => (hsmall i y hy.1).1
  have hfirst (x : NormalizedState) (hp : positiveWalls x) (hc : stateConstraint x = 1)
      (hx : x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h) B (Ici 0)) :
      IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h) B (Ici 0) x) (τ x) ∧
        ∃ w ∈ axisFamilySection E \ F, axisFamilyChart primaryAxisFrame (fun _ => h) w = Y x := by
    have H := globalAxisWallFirstTime_small_target primaryAxisFrame (fun _ => hh) (fun _ => hh1)
      hp hc (Subset.refl _) (fun i y hy => hsmall i y hy.1) hx
    obtain ⟨i, y, hy, heq⟩ := H.1.2.2
    exact ⟨H, (i, y), hy, heq⟩
  refine ⟨τ, Y, measurable_globalAxisWallFirstTime primaryAxisFrame (fun _ => hh) hB measurableSet_Ici hchart,
    measurable_globalAxisWallFirstState primaryAxisFrame (fun _ => hh) hB measurableSet_Ici hchart,
    fun _ => rfl, hfirst, ?_⟩
  filter_upwards [ae_smallAxis_success_hitting hh hh1 hE hsmall hF hfinite] with z hz hrec
  exact hfirst _ (axisWallChart_positive (primaryAxisFrame z.1) hh z.2)
    (axisWallChart_constraint (primaryAxisFrame z.1) (hsmall z.1 z.2 hrec.1).1) (hz hrec)

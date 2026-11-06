-- Prove2me | solution 1 for BianchiIX.exists_compact_core_factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:51:45.903383+00:00
-- url     : https://prove2.me/submissions/3a176dd4-af36-4332-a8b0-1ec1768b032f

import Definitions.Def_BianchiIX_Analysis_CoordinateFactor
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
import Theorems.Thm_BianchiIX_compactCoreFactor_reference_value
import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_exists_compact_core_factorization
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiff_coordinateSegment {n : ℕ} (i : Fin n) (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun p : (Fin n → ℝ) × ℝ => coordinateSegment i p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simp only [coordinateSegment, Function.update_self]
    fun_prop
  · simp only [coordinateSegment, Function.update_of_ne h]
    fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_coordinateFactor {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    ContDiffAt ℝ 1 (coordinateFactor f i) Y := by
  apply contDiffAt_intervalIntegral_of_contDiffAt
    (F := fun p => fderiv ℝ f (coordinateSegment i p.1 p.2) (Pi.single i 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  have hD := ((hf s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp (Y, s)
    (contDiff_coordinateSegment i 1).contDiffAt
  exact hD.clm_apply contDiffAt_const

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.compactCoreFactor_reference_bounds {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    0 < compactCoreFactor ![k, 0, 0] i ∧ compactCoreFactor ![k, 0, 0] i < 1 := by
  rw [compactCoreFactor_reference_value hk i]
  have hL := Real.arcosh_pos hk
  have hk0 : 0 < k := by linarith only [hk]
  split_ifs
  · exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hk0) hL)⟩
  · exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hL) hk0)⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_compactCoreFactor_reference {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    ContDiffAt ℝ 1 (fun Y => compactCoreFactor Y i) ![k, 0, 0] := by
  apply contDiffAt_coordinateFactor
  intro s _
  have hzero : (![k, 0, 0] : CoreAngleState) i.succ = 0 := by fin_cases i <;> rfl
  have hseg : coordinateSegment i.succ (![k, 0, 0] : CoreAngleState) s = ![k, 0, 0] := by
    simp only [coordinateSegment, hzero, mul_zero]
    exact Function.update_eq_self_iff.mpr hzero.symm
  rw [hseg]
  exact contDiffAt_pi.mp (coreRadiusReturn_reference_regular hk).2.2.1 i.succ

end
end

/-- Positive compact-core factors have a common strict contraction and bounded logarithmic derivatives. -/
theorem solution :
    ∃ ε > (0 : ℝ), ∃ q > (0 : ℝ), q < 1 ∧ ∃ C > (0 : ℝ),
      ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
          ∀ i : Fin 2,
            coreReturnState coreRadiusReturnTime Y i.succ = Y i.succ * compactCoreFactor Y i ∧
            0 < compactCoreFactor Y i ∧ compactCoreFactor Y i ≤ q ∧
            ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
            ContDiffAt ℝ 1 (fun Z => Real.log (compactCoreFactor Z i)) Y ∧
            ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y‖ ≤ C ∧
            (∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i) := by
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSne : S.Nonempty := ⟨![2, 0, 0], 2, by norm_num, rfl⟩
  have hreg (Y : CoreAngleState) (hY : Y ∈ S) (i : Fin 2) :
      ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
        0 < compactCoreFactor Y i ∧ compactCoreFactor Y i < 1 := by
    obtain ⟨k, hk, rfl⟩ := hY
    have hk1 : 1 < k := by linarith only [hk.1]
    exact ⟨contDiffAt_compactCoreFactor_reference hk1 i, compactCoreFactor_reference_bounds hk1 i⟩
  have hc (i : Fin 2) : ContinuousOn (fun Y => compactCoreFactor Y i) S :=
    fun Y hY => (hreg Y hY i).1.continuousAt.continuousWithinAt
  have hcmax : ContinuousOn (fun Y => max (compactCoreFactor Y 0) (compactCoreFactor Y 1)) S :=
    (continuous_fst.max continuous_snd).comp_continuousOn ((hc 0).prodMk (hc 1))
  obtain ⟨Z, hZS, hmax⟩ := hS.exists_isMaxOn hSne hcmax
  let q₀ := max (compactCoreFactor Z 0) (compactCoreFactor Z 1)
  have hq₀ : 0 < q₀ := lt_of_lt_of_le (hreg Z hZS 0).2.1 (le_max_left _ _)
  have hq₀1 : q₀ < 1 := max_lt (hreg Z hZS 0).2.2 (hreg Z hZS 1).2.2
  let q := (q₀ + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith only [hq₀]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hq₀1]
  have hq₀q : q₀ < q := by dsimp [q]; linarith only [hq₀1]
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) (i : Fin 2) : compactCoreFactor Y i < q := by
    apply lt_of_le_of_lt _ hq₀q
    have H := hmax hY
    fin_cases i
    · exact (le_max_left _ _).trans H
    · exact (le_max_right _ _).trans H
  let G : Set CoreAngleState := {Y | ∀ i : Fin 2,
    ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
      0 < compactCoreFactor Y i ∧ compactCoreFactor Y i < q}
  have hSG : S ⊆ interior G := by
    intro Y hY
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨hdi, hpos, _⟩ := hreg Y hY i
    exact (hdi.eventually (by norm_num)).and
      ((hdi.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)).and
        (hdi.continuousAt.eventually (isOpen_Iio.mem_nhds (hbound Y hY i))))
  obtain ⟨δ, hδ, hδG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening δ S
  have hWG : W ⊆ G := hδG.trans interior_subset
  have hlog (Y : CoreAngleState) (hY : Y ∈ W) (i : Fin 2) :
      ContDiffAt ℝ 1 (fun Z => Real.log (compactCoreFactor Z i)) Y :=
    (hWG hY i).1.log (ne_of_gt (hWG hY i).2.1)
  let b : CoreAngleState → ℝ := fun Y =>
    ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z 0)) Y‖ +
      ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z 1)) Y‖
  have hcb : ContinuousOn b W := fun Y hY =>
    (((hlog Y hY 0).continuousAt_fderiv (by norm_num)).norm.add
      ((hlog Y hY 1).continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.cthickening.exists_bound_of_continuousOn hcb
  obtain ⟨ε₀, hε₀, hfactor⟩ := exists_compact_core_factorization
  let ε := min ε₀ δ
  refine ⟨ε, lt_min hε₀ hδ, q, hq, hq1, max B 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hY := hfactor Y hk (hu.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ δ := by
    apply (dist_pi_le_iff hδ.le).mpr
    intro i
    fin_cases i
    · simpa using hδ.le
    · simpa [Real.dist_eq] using hu.trans (min_le_right ε₀ δ)
    · simpa [Real.dist_eq] using hw.trans (min_le_right ε₀ δ)
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ δ S ⟨Y 0, hk, rfl⟩ hdist
  refine ⟨hY.1, hY.2.1, ?_⟩
  intro i
  refine ⟨(hY.2.2 i).2.1, (hWG hYW i).2.1, (hWG hYW i).2.2.le,
    (hWG hYW i).1, hlog Y hYW i, ?_, (hY.2.2 i).2.2⟩
  have H : b Y ≤ max B 1 := (le_abs_self _).trans ((hB Y hYW).trans (le_max_left _ _))
  fin_cases i
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans H
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans H

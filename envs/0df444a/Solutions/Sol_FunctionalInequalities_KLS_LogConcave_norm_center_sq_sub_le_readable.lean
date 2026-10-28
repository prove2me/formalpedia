-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:25:02.321659+00:00
-- url     : https://prove2.me/submissions/be05fd46-546f-4354-80f2-adae9575599a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Markov
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Decay
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_sq_sub_norm_apply_sq_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_center_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_mul_norm_closedWeightedOperator_sq_le_readable

section
noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
open scoped RealInnerProductSpace
section
variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (μ : MeasureTheory.ProbabilityMeasure α)
variable {μ : MeasureTheory.ProbabilityMeasure α} {T : MeasureTheory.Lp ℝ 2 (μ : MeasureTheory.Measure α) →ₗ.[ℝ] H}
/-- If one lies in the form domain and has zero energy, every resolvent fixes it. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    resolventCLM T hT hs (L2.const μ 1) = L2.const μ 1 := by
  let oneDom : T.domain := ⟨L2.const μ 1, hone⟩
  have hweak : WeakResolvent T s (L2.const μ 1) oneDom := by
    intro v
    change ⟪L2.const μ 1, (v : Lp ℝ 2 (μ : Measure α))⟫ + s * ⟪T oneDom, T v⟫ = _
    rw [hTone, inner_zero_left, mul_zero, add_zero]
  rw [resolventCLM_apply, ← eq_resolventDomain T hT hs hweak]
omit [CompleteSpace H] in
/-- Exponentiating an operator that kills `f` fixes `f`. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_apply_of_apply_eq_zero
    (A : Lp ℝ 2 (μ : Measure α) →L[ℝ] Lp ℝ 2 (μ : Measure α))
    (f : Lp ℝ 2 (μ : Measure α)) (hAf : A f = 0) : NormedSpace.exp A f = f := by
  have hsum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL
    (ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ : Measure α)) f)
  apply hsum.unique
  convert hasSum_ite_eq 0 f using 1
  ext n
  rcases n with _ | n
  · simp
  · simp [pow_succ, hAf]
/-- If the resolvent fixes one, its Yosida approximation kills one. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.yosida_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    yosida T hT hs (L2.const μ 1) = 0 := by
  rw [yosida_apply, resolventCLM_one hT hs hone hTone, sub_self, smul_zero]
/-- Every Yosida exponential fixes one. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (t : ℝ)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    NormedSpace.exp (-t • yosida T hT hs) (L2.const μ 1) = L2.const μ 1 := by
  apply exp_apply_of_apply_eq_zero
  change -t • yosida T hT hs (L2.const μ 1) = 0
  rw [yosida_one hT hs hone hTone, smul_zero]
end
section
open FunctionalInequalities.Analysis.Semigroup.LpMarkov
variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : MeasureTheory.ProbabilityMeasure α} {T : MeasureTheory.Lp ℝ 2 (μ : MeasureTheory.Measure α) →ₗ.[ℝ] H}
/-- If the form kills one, the generated semigroup fixes one. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.one (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2
    (μ : Measure α)))) {t : ℝ} (ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    Generated.apply T hT hd t (L2.const μ 1) = L2.const μ 1 := by
  refine (Generated.eq_apply_of_tendsto T hT hd ht (L2.const μ 1) (L2.const μ 1) ?_).symm
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro s hs _
  rw [exp_neg_smul_yosida_one hT hs t hone hTone, sub_self, norm_zero]
  exact hε
/-- Symmetry and preservation of one imply preservation of the `L²` mean. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.mean (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2
    (μ : Measure α)))) {t : ℝ} (ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0)
    (f : Lp ℝ 2 (μ : Measure α)) :
    L2.mean μ (Generated.apply T hT hd t f) = L2.mean μ f := by
  rw [L2.mean, Generated.symmetric T hT hd ht,
    Generated.one hT hd ht hone hTone]
  rfl
end
end
end

section
noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
open scoped RealInnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
section
/-- The heat semigroup fixes the constant one. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.one (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht (L2.const ν 1) = L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.one
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero_readable m B hν hi)
/-- The heat semigroup preserves the `L²` mean. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mean (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) :
    L2.mean ν (HeatSemigroup.operator m B hν hi ht f) = L2.mean ν f := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.mean
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero_readable m B hν hi) f
end
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- The actual heat operator fixes every L2 constant. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.const_fixed {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    operator m B hν hi ht (L2.const ν c) = L2.const ν c := by
  have hc : L2.const ν c = c • L2.const ν 1 := by
    simpa using L2.const_smul ν c 1
  rw [hc, map_smul]
  simp only [one m B hν hi ht]
/-- Centering commutes with the actual heat operator. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_operator {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν (operator m B hν hi ht f) =
      operator m B hν hi ht (L2.center ν f) := by
  rw [L2.center, L2.center, HeatSemigroup.mean m B hν hi ht f, map_sub,
    const_fixed m B hν hi ht]
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
include hνU hU in
/-- The finite-time Poincaré bound: if `∇∇U ≥ ρ > 0`, then for `u ∈ D(T̄)` and `t ≥ 0`,
`Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖T̄ u‖²`. -/
theorem solution {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖FunctionalInequalities.L2.center ν
          (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  let c : T.domain :=
    ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩

  have hcurv :
      ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain,
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    intro y
    exact FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le_readable m hν hi hνU hU hH y

  have hkey :=
    FunctionalInequalities.Analysis.Semigroup.Generated.norm_sq_sub_norm_apply_sq_le_readable T hT hd hρ hcurv c ht

  have hcenter :
      FunctionalInequalities.L2.center ν
          (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            (u : Lp ℝ 2 (ν : Measure V))) =
        FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))) := by
    exact FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_operator m (ContinuousLinearMap.id ℝ V) hν hi ht
      (u : Lp ℝ 2 (ν : Measure V))

  rw [hcenter]

  change
    ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t c‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖T u‖ ^ 2

  have hTc :
      T c = T u := by
    simpa [c, T] using
      (FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_readable m hν hi u)

  rw [hTc] at hkey
  exact hkey

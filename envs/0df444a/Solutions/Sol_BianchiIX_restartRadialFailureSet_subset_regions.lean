-- Prove2me | solution 1 for BianchiIX.restartRadialFailureSet_subset_regions
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:07:12.6132+00:00
-- url     : https://prove2.me/submissions/9b8dfb65-bfb6-44e6-8a83-058a43e44107

import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Theorems.Thm_BianchiIX_angularRadialFailure_subset_layer
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory

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
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallReflection_mem_symmetrization_iff {A : Set SectionCoordinates} {y : SectionCoordinates} :
    mainWallReflection y ∈ mainWallSymmetrization A ↔ y ∈ mainWallSymmetrization A := by
  change (mainWallReflection y ∈ A ∨ mainWallReflection y ∈ mainWallReflection '' A) ↔
    (y ∈ A ∨ y ∈ mainWallReflection '' A)
  constructor
  · rintro (h | ⟨z, hz, heq⟩)
    · exact Or.inr ⟨mainWallReflection y, h, mainWallReflection_twice y⟩
    · exact Or.inl ((mainWallReflectionEquiv.injective heq) ▸ hz)
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inr ⟨y, h, rfl⟩
    · exact Or.inl (by simpa only [mainWallReflection_twice] using hz)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledShearLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledShearLogCoordinates a) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (a * z 1) = -Real.log (a * w 1) at h1
  change -Real.log (a * z 2) = -Real.log (a * w 2) at h2
  have H1 := Real.log_injOn_pos (mul_pos ha hz.1) (mul_pos ha hw.1) (neg_injective h1)
  have H2 := Real.log_injOn_pos (mul_pos ha hz.2) (mul_pos ha hw.2) (neg_injective h2)
  ext i
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ ha.ne' H1
  · exact mul_left_cancel₀ ha.ne' H2

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

private theorem BianchiIX.restartShearAmplitudeBudget_le_of_min {a n₂ n₃ P : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hP : 4 ≤ P) (h₂ : 0 < n₂ ∧ n₂ ≤ a)
    (h₃ : 0 < n₃ ∧ n₃ ≤ a) (hmin : min n₂ n₃ ≤ a ^ P) :
    0 < restartShearAmplitudeBudget a n₂ n₃ ∧ restartShearAmplitudeBudget a n₂ n₃ ≤ 800 * a := by
  have hp : a ^ P ≤ a ^ (4 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2 hP
  have hprod : n₂ * n₃ ≤ a * a ^ 4 := by
    rcases min_le_iff.mp hmin with hsmall | hsmall
    · exact (mul_le_mul (hsmall.trans hp) h₃.2 h₃.1.le (by positivity)).trans_eq (mul_comm _ _)
    · exact mul_le_mul h₂.2 (hsmall.trans hp) h₃.1.le ha.1.le
  refine ⟨by dsimp [restartShearAmplitudeBudget]; positivity [ha.1, h₂.1, h₃.1], ?_⟩
  calc
    _ = 800 * (n₂ * n₃) / a ^ 4 := by unfold restartShearAmplitudeBudget; ring
    _ ≤ 800 * (a * a ^ 4) / a ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
    _ = _ := by field_simp

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
open EraSurvivor

private theorem BianchiIX.eraSelectedInputs_mono_cap {η σ B₁ B₂ : ℝ} {J m : ℕ} (hB : B₁ ≤ B₂) :
    eraSelectedInputs η J σ B₁ m ⊆ eraSelectedInputs η J σ B₂ m := by
  intro p hp
  exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hB⟩, hp.1.2⟩, hp.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open EraSurvivor

private theorem BianchiIX.eraPrefixDomain_mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ} (hB : B₁ ≤ B₂) (w : List ℕ+) :
    eraPrefixDomain η J σ B₁ w ⊆ eraPrefixDomain η J σ B₂ w := by
  induction w with
  | nil => exact Subset.refl _
  | cons a w ih =>
    intro p hp
    exact ⟨eraSelectedInputs_mono_cap hB hp.1, ih hp.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open EraSurvivor

private theorem BianchiIX.eraPrefixDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ} {w : List ℕ+}
    {p : ℝ × CoreAngleState} (hp : p ∈ eraPrefixDomain η J σ B₁ w)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ eraPrefixDomain η J σ B₂ w := by
  induction w generalizing p with
  | nil => exact Set.mem_univ _
  | cons a w ih =>
    have hstep : (eraBudgetReturn η J a.natPred p).1 ≤ p.1 :=
      Real.rpow_le_self_of_le_one hp.1.1.1.1.le hone (by norm_num)
    exact ⟨⟨⟨⟨hp.1.1.1.1, hB⟩, hp.1.1.2⟩, hp.1.2⟩,
      ih hp.2 (hstep.trans hone) (hstep.trans hB)⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open EraSurvivor

private theorem BianchiIX.eraSurvivorDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {p : ℝ × CoreAngleState} (hp : p ∈ eraSurvivorDomain η J σ B₁)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ eraSurvivorDomain η J σ B₂ := by
  apply mem_iInter.mpr
  intro n
  obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
  exact mem_iUnion.mpr ⟨w, eraPrefixDomain_restrict_cap hw hone hB⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open EraSurvivor

private theorem BianchiIX.EraSurvivor.word_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) (n : ℕ) : word p n = word q n := by
  apply eraPrefixDomain_unique η J σ (max B₁ B₂) ((word_length p n).trans (word_length q n).symm)
    (eraPrefixDomain_mono_cap (le_max_left B₁ B₂) _ (mem_word_domain p n))
  rw [hpq]
  exact eraPrefixDomain_mono_cap (le_max_right B₁ B₂) _ (mem_word_domain q n)

end
end

section
noncomputable section
open BianchiIX
open Set
open EraSurvivor

private theorem BianchiIX.EraSurvivor.digits_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) : digits p = digits q := by
  funext n
  have H := (word_succ p n).symm.trans ((word_eq_of_val p q hpq (n + 1)).trans (word_succ q n))
  rw [word_eq_of_val p q hpq n] at H
  exact List.singleton_inj.mp (List.append_inj_right H rfl)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EraSurvivor.typicalDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {p : ℝ × CoreAngleState} (hp : p ∈ typicalDomain η J σ B₁)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ typicalDomain η J σ B₂ := by
  rcases hp with ⟨q, hq, rfl⟩
  let r : eraSurvivorDomain η J σ B₂ := ⟨q.val, eraSurvivorDomain_restrict_cap q.property hone hB⟩
  refine ⟨r, ?_, rfl⟩
  change gaussCode (digits r) ∈ gaussCylinderTypicalSet
  rw [← digits_eq_of_val q r rfl]
  exact hq

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraRadialFailure_subset_of_budget {η σ B B₁ B₂ a b : ℝ} {J : ℕ}
    (hone : B ≤ 1) (hB : B ≤ B₂) (Y : ℝ → CoreAngleState) :
    eraRadialFailure η J σ B B₂ a b Y ⊆ eraRadialFailure η J σ B B₁ a b Y := by
  intro r hr
  exact ⟨hr.1, fun hg => hr.2 (EraSurvivor.typicalDomain_restrict_cap hg hone hB)⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mem_shearLabelFailureSection_image_iff {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} {z : SectionCoordinates} (ha : 0 < a) (hz : 0 < z 1 ∧ 0 < z 2) :
    scaledShearLogCoordinates a z ∈ shearLabelFailureSection a L F ↔
      z ∈ shearLabelFailureCoordinates a L F := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact scaledShearLogCoordinates_injOn ha ⟨hw.1.1, hw.2.1.1⟩ hz heq ▸ hw
  · exact fun hw => ⟨z, hw, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal Classical

private theorem BianchiIX.mem_shearLabelFailureSection_iff {a n₂ n₃ ρ : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (h₂ : n₂ ∈ Ioo 0 a) (h₃ : n₃ ∈ Ioo 0 a)
    (hl : (n₂, n₃) ∈ L) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ shearLabelFailureSection a L F ↔ ρ ∈ F (n₂, n₃) := by
  have hx : n₂ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₂.1 ha, (div_lt_one ha).mpr h₂.2⟩
  have hy : n₃ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₃.1 ha, (div_lt_one ha).mpr h₃.2⟩
  have h₂a : a * (n₂ / a) = n₂ := mul_div_cancel₀ _ ha.ne'
  have h₃a : a * (n₃ / a) = n₃ := mul_div_cancel₀ _ ha.ne'
  have H := mem_shearLabelFailureSection_image_iff (L := L) (F := F)
    (z := ![ρ, n₂ / a, n₃ / a]) ha ⟨hx.1, hy.1⟩
  simpa [scaledShearLogCoordinates, shearLabelFailureCoordinates, h₂a, h₃a,
    hx.1, hx.2, hy.1, hy.2, hl] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mem_restartShearCommonFailureSection_iff {h s a ε P η σ Bcap n₂ n₃ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hε : ε ≤ 1 / 128) (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε a P) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ restartShearCommonFailureSection h s a ε P η J σ Bcap ↔
      ρ ∈ restartShearFailureFibers h s a η J σ Bcap (n₂, n₃) := by
  have hs : 2 * ε < 1 := by linarith only [hε]
  exact mem_shearLabelFailureSection_iff ha
    ⟨hl.1.1, hl.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩
    ⟨hl.2.1.1, hl.2.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩ hl

end
end

private theorem BianchiIX.shearUnselectedSection_reflection (a ε P : ℝ) (z : SectionCoordinates) :
    mainWallReflection z ∈ shearUnselectedSection a ε P ↔ z ∈ shearUnselectedSection a ε P := by
  simp [shearUnselectedSection, shearSectionLayer, mainWallReflection, and_left_comm, and_comm, and_assoc]

private theorem BianchiIX.shearRadialDomain_swap {a d ε : ℝ} {z : SectionCoordinates}
    (hz : z ∈ shearRadialDomain a d ε) : ![z 0, z 2, z 1] ∈ shearRadialDomain a d ε := by
  refine ⟨hz.2.1, hz.1, hz.2.2.1, ?_, hz.2.2.2.2⟩
  change max (z 2) (z 1) ≤ ε * z 0
  simpa only [max_comm] using hz.2.2.2.1

private theorem BianchiIX.shearRadialFailure_subset_layer {h s a d ε P η σ Bcap Bother : ℝ} {J : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hsmall : 800 * a ≤ Bcap) {z : SectionCoordinates}
    (hz : z ∈ shearRadialDomain a d ε)
    (hf : z ∈ labelRadialFailure a (restartShearCommonLabelSet ε a P)
      (EraSurvivor.typicalDomain η J σ Bcap)
      (fun l r => (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 r))) :
    signedShearLogCoordinates 1 z ∈
      mainWallSymmetrization (restartShearCommonFailureSection h s a ε P η J σ Bother) ∪
        shearUnselectedSection a ε P := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hn : max (z 1) (z 2) ≤ 2 * ε * a :=
    hz.2.2.2.1.trans ((mul_le_mul_of_nonneg_left hz.2.2.1.2.le hε.1).trans_eq (by ring))
  have h₂ : 0 < z 1 ∧ z 1 ≤ 2 * ε * a := ⟨hz.1, (le_max_left _ _).trans hn⟩
  have h₃ : 0 < z 2 ∧ z 2 ≤ 2 * ε * a := ⟨hz.2.1, (le_max_right _ _).trans hn⟩
  by_cases hl : (z 1, z 2) ∈ restartShearCommonLabelSet ε a P
  · have hεa : 2 * ε * a ≤ a := by nlinarith only [ha, hε.2]
    have hb := (restartShearAmplitudeBudget_le_of_min ⟨ha, ha1⟩ hP
      ⟨h₂.1, h₂.2.trans hεa⟩ ⟨h₃.1, h₃.2.trans hεa⟩ hl.2.2).2.trans hsmall
    have hbad : z 0 ∈ restartShearFailureFibers h s a η J σ Bother (z 1, z 2) :=
      eraRadialFailure_subset_of_budget (hb.trans hcap) hb _ ⟨hf.1, hf.2.resolve_left (not_not.mpr hl)⟩
    have H := (mem_restartShearCommonFailureSection_iff ha hε.2 hl).mpr hbad
    exact Or.inl (Or.inl (by simpa [signedShearLogCoordinates] using H))
  · have hm : a ^ P < min (z 1) (z 2) := lt_of_not_ge (fun H => hl ⟨h₂, h₃, H⟩)
    apply Or.inr
    simpa [signedShearLogCoordinates, abs_of_pos hr, Real.exp_log hz.1,
      Real.exp_log hz.2.1, shearUnselectedSection, shearSectionLayer] using
      (show (z 0 ∈ Icc a (2 * a) ∧ z 1 ≤ 2 * ε * a ∧ z 2 ≤ 2 * ε * a) ∧
        a ^ P < z 1 ∧ a ^ P < z 2 from
        ⟨⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, h₂.2, h₃.2⟩, (lt_min_iff.mp hm).1, (lt_min_iff.mp hm).2⟩)


/-- Comparison caps need not agree: small actual budgets retain the identical statistical history. -/
theorem solution {h q d ε P η σ Bcap BA BS : ℝ} {J : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hL : 0 ≤ 1 / ε) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hS : 800 * d ≤ Bcap) (hA : 51200 * (1 / ε + 1) * d ≤ Bcap) :
    radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap) ⊆
      mainWallRadialBoundary d ε ∪
        (angularFailureRegion h q d (1 / ε) P η J σ BA ∪ shearFailureRegion h q d ε P η J σ BS) := by
  rintro y (hb | hf)
  · exact Or.inl hb
  · apply Or.inr
    obtain ⟨⟨k, j⟩, z, ⟨hz, hbad⟩, rfl⟩ := mem_iUnion.mp hf
    have ha := dyadicScale_pos hd j
    have had := dyadicScale_le hd.le j
    have ha1 := had.trans hd1
    have hSa : 800 * dyadicScale d j ≤ Bcap :=
      (mul_le_mul_of_nonneg_left had (by norm_num)).trans hS
    have hAa : 51200 * (1 / ε + 1) * dyadicScale d j ≤ Bcap :=
      (mul_le_mul_of_nonneg_left had (by positivity)).trans hA
    rcases k with neg | other
    · have H : radialPieceMap (Sum.inl neg) z ∈
          mainWallSymmetrization (restartShearCommonFailureSection h
            (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ BS) ∪
              shearUnselectedSection (dyadicScale d j) ε P := by
        cases neg
        · exact shearRadialFailure_subset_layer ha ha1 hε hP hcap hSa hz hbad
        · have H := shearRadialFailure_subset_layer (Bother := BS) ha ha1 hε hP hcap hSa
            (shearRadialDomain_swap hz) hbad
          have heq : radialPieceMap (Sum.inl true) z =
              mainWallReflection (signedShearLogCoordinates 1 ![z 0, z 2, z 1]) := by
            ext i
            fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, mainWallReflection]
          rw [heq]
          rcases H with hs | hu
          · exact Or.inl (mainWallReflection_mem_symmetrization_iff.mpr hs)
          · exact Or.inr ((shearUnselectedSection_reflection _ _ _ _).mpr hu)
      rcases H with hs | hu
      · exact Or.inr (Or.inl (mem_iUnion_of_mem j hs))
      · exact Or.inr (Or.inr (mem_iUnion_of_mem j hu))
    · have H := angularRadialFailure_subset_layer (Bother := BA) ha ha1 hL hP hcap hAa other hz hbad
      rcases H with hs | hu
      · exact Or.inl (Or.inl (mem_iUnion_of_mem j hs))
      · exact Or.inl (Or.inr (mem_iUnion_of_mem j hu))

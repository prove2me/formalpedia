-- Prove2me | solution 1 for BianchiIX.angularRadialFailure_subset_layer
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:05:50.726402+00:00
-- url     : https://prove2.me/submissions/b6570dee-d324-4751-85a1-715fce2adb76

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
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
open Set MeasureTheory

private theorem BianchiIX.mem_restartAngularFailureSection_iff {h s a L P η σ Bcap θ ζ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hθ : |θ| ≤ L) (hζ : 0 < ζ ∧ ζ < 2 * a) (hl : ζ ≤ a ^ P) (hρ : 0 < ρ) :
    ![θ * ρ, -Real.log ρ, -Real.log ζ] ∈ restartAngularFailureSection h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
  let z : SectionCoordinates := ![ρ, θ, ζ / (2 * a)]
  have ht : ζ / (2 * a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hζ.1 (by positivity), (div_lt_one (by positivity)).mpr hζ.2⟩
  have heq : 2 * a * (ζ / (2 * a)) = ζ := mul_div_cancel₀ _ (by positivity)
  have hmap : scaledAngularLogCoordinates a z = ![θ * ρ, -Real.log ρ, -Real.log ζ] := by
    simp [scaledAngularLogCoordinates, z, heq]
  have hmember : z ∈ restartAngularFailureCoordinates h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
    simp [restartAngularFailureCoordinates, z, heq, ht.1, ht.2, restartLabelSet, hθ, hl, hζ.1,
      (abs_le.mp hθ).1, (abs_le.mp hθ).2]
  rw [← hmap, ← hmember]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwpos : 0 < w 0 ∧ 0 < w 2 := ⟨ha.trans_le hw.2.2.2.1.1, hw.2.1.1⟩
    exact (scaledAngularLogCoordinates_injOn ha hwpos ⟨hρ, ht.1⟩ hwz) ▸ hw
  · exact fun hz => ⟨z, hz, rfl⟩

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
open scoped ENNReal

private theorem BianchiIX.restartAmplitudeBudget_le_scale {L a ζ P : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (haone : a ≤ 1) (hP : 4 ≤ P) (hζ : ζ ≤ a ^ P) :
    restartAmplitudeBudget L a ζ ≤ 51200 * (L + 1) * a := by
  have hζ4 : ζ ≤ a ^ (4 : ℕ) := hζ.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha haone hP)
  calc
    _ ≤ 6400 * (8 * (L + 1)) * a ^ 4 / a ^ 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hζ4 (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

end
end

private theorem BianchiIX.angularUnselectedSection_reflection (a L P : ℝ) (z : SectionCoordinates) :
    mainWallReflection z ∈ angularUnselectedSection a L P ↔ z ∈ angularUnselectedSection a L P := by
  change (max (Real.exp (-z 2)) (Real.exp (-z 1)) ∈ Icc a (2 * a) ∧
    |-z 0| ≤ L * max (Real.exp (-z 2)) (Real.exp (-z 1)) ∧
    a ^ P < min (Real.exp (-z 2)) (Real.exp (-z 1))) ↔ _
  rw [max_comm (Real.exp (-z 2)) (Real.exp (-z 1)),
    min_comm (Real.exp (-z 2)) (Real.exp (-z 1)), abs_neg]
  rfl


/-- The angular comparison retains the smaller-wall cutoff and the fixed original label. -/
theorem solution {h s a d L P η σ Bcap Bother : ℝ} {J : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hL : 0 ≤ L) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hsmall : 51200 * (L + 1) * a ≤ Bcap)
    (other : Bool) {z : SectionCoordinates} (hz : z ∈ angularRadialDomain other a d L)
    (hf : z ∈ labelRadialFailure a (restartLabelSet L a P)
      (EraSurvivor.typicalDomain η J σ Bcap)
      (fun l r => (restartAmplitudeBudget L a l.2, restartReturnState h s l.1 l.2 r))) :
    orderedAngularLogCoordinates other z ∈
      mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bother) ∪
        angularUnselectedSection a L P := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho : z 2 ≤ z 0 := by
    have H := hz.2.2.2.1
    cases other
    · exact H
    · exact le_of_lt H
  have hζ : 0 < z 2 ∧ z 2 < 2 * a := ⟨hz.2.1, ho.trans_lt hz.2.2.1.2⟩
  have hbase : scaledAngularLogCoordinates (1 / 2) z ∈
      mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bother) ∪
        angularUnselectedSection a L P := by
    by_cases hl : (z 1, z 2) ∈ restartLabelSet L a P
    · have hb := (restartAmplitudeBudget_le_scale hL ha ha1 hP hl.2.2).trans hsmall
      have hbad : z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (z 2)) Bother a (2 * a)
          (restartReturnState h s (z 1) (z 2)) :=
        eraRadialFailure_subset_of_budget (hb.trans hcap) hb _ ⟨hf.1, hf.2.resolve_left (not_not.mpr hl)⟩
      have H := (mem_restartAngularFailureSection_iff ha hz.1.le hζ hl.2.2 hr).mpr hbad
      exact Or.inl (Or.inl (by simpa [scaledAngularLogCoordinates] using H))
    · have hζlow : a ^ P < z 2 := lt_of_not_ge (fun H => hl ⟨hz.1.le, hz.2.1, H⟩)
      apply Or.inr
      have hθ := mul_le_mul_of_nonneg_right hz.1.le hr.le
      have heq : scaledAngularLogCoordinates (1 / 2) z = ![z 1 * z 0, -Real.log (z 0), -Real.log (z 2)] := by
        ext i
        fin_cases i <;> simp [scaledAngularLogCoordinates]
      rw [heq]
      change max (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2))) ∈ Icc a (2 * a) ∧
        |z 1 * z 0| ≤ L * max (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2))) ∧
        a ^ P < min (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2)))
      simp only [neg_neg, Real.exp_log hr, Real.exp_log hz.2.1,
        max_eq_left ho, min_eq_right ho, abs_mul, abs_of_pos hr]
      exact ⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, hθ, hζlow⟩
  cases other
  · exact hbase
  · rcases hbase with hs | hu
    · exact Or.inl (mainWallReflection_mem_symmetrization_iff.mpr hs)
    · exact Or.inr ((angularUnselectedSection_reflection a L P _).mpr hu)

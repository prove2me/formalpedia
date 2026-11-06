-- Prove2me | solution 1 for BianchiIX.EraSurvivor.physicalTime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:33:26.017069+00:00
-- url     : https://prove2.me/submissions/17007a98-bec9-43f0-aca2-118ddb8e0260

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

section
open BianchiIX
open Set

private theorem BianchiIX.measurable_comp_of_continuousAt {X Y Z : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {g : X → Y} {f : Y → Z} (hg : Measurable g)
    (hf : ∀ x, ContinuousAt f (g x)) : Measurable (f ∘ g) := by
  have hc : ContinuousOn f (range g) := by
    rintro _ ⟨x, rfl⟩
    exact (hf x).continuousWithinAt
  have hg' : Measurable (fun x => (⟨g x, mem_range_self x⟩ : range g)) := hg.subtype_mk
  exact hc.domRestrict.measurable.comp hg'

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

private theorem BianchiIX.eraPrefixDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val))
    (w : List ℕ+) : MeasurableSet (eraPrefixDomain η J σ Bstar w) ∧
      Measurable (fun p : eraPrefixDomain η J σ Bstar w => eraPrefixState η J w p.val) := by
  induction w with
  | nil => exact ⟨MeasurableSet.univ, measurable_subtype_coe⟩
  | cons a w ih =>
    let S := eraSelectedInputs η J σ Bstar a.natPred
    let D := eraPrefixDomain η J σ Bstar w
    let Q := eraBudgetReturn η J a.natPred
    have hA : MeasurableSet {p : S | Q p.val ∈ D} := ih.1.preimage (H a.natPred).2
    have heq : eraPrefixDomain η J σ Bstar (a :: w) = Subtype.val '' {p : S | Q p.val ∈ D} := by
      ext p
      constructor
      · exact fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.property, hp⟩
    refine ⟨by rw [heq]; exact (H a.natPred).1.subtype_image hA, ?_⟩
    have hi : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨p.val, p.property.1⟩ : S)) :=
      measurable_subtype_coe.subtype_mk
    have hQ : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => Q p.val) :=
      (H a.natPred).2.comp hi
    have hmap : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨Q p.val, p.property.2⟩ : D)) :=
      hQ.subtype_mk
    exact ih.2.comp hmap

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.word_eq_iff (p : eraSurvivorDomain η J σ Bstar) {n : ℕ} {w : List ℕ+} (hw : w.length = n) :
    word p n = w ↔ p.val ∈ eraPrefixDomain η J σ Bstar w := by
  constructor
  · exact fun h => h ▸ mem_word_domain p n
  · exact fun h => eraPrefixDomain_unique η J σ Bstar ((word_length p n).trans hw.symm) (mem_word_domain p n) h

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
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.digit_fiber (n : ℕ) (a : ℕ+) :
    {p : eraSurvivorDomain η J σ Bstar | digits p n = a} =
      ⋃ w : {w : List ℕ+ // w.length = n},
        (Subtype.val : eraSurvivorDomain η J σ Bstar → ℝ × CoreAngleState) ⁻¹'
          eraPrefixDomain η J σ Bstar (w.val ++ [a]) := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · intro h
    refine ⟨⟨word p n, word_length p n⟩, ?_⟩
    simpa only [word_succ, h] using mem_word_domain p (n + 1)
  · rintro ⟨⟨w, hw⟩, hp⟩
    have heq := (word_eq_iff p (by simp [hw] : (w ++ [a]).length = n + 1)).mpr hp
    rw [word_succ] at heq
    exact List.singleton_inj.mp (List.append_inj_right heq ((word_length p n).trans hw.symm))

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.digits_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (digits (η := η) (J := J) (σ := σ) (Bstar := Bstar)) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro a
  change MeasurableSet {p : eraSurvivorDomain η J σ Bstar | digits p n = a}
  rw [digit_fiber]
  exact MeasurableSet.iUnion (fun w =>
    ((eraPrefixDomain_measurable H (w.val ++ [a])).1).preimage measurable_subtype_coe)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_mem_selected (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p n ∈ eraSelectedInputs η J σ Bcap (digits p n).natPred := by
  have H := mem_word_domain p (n + 1)
  rw [word_succ] at H
  exact ((mem_eraPrefixDomain_append η J σ Bcap (word p n) [digits p n] p.val).mp H).2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))
include H

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.word_measurable (n : ℕ) :
    Measurable (fun p : eraSurvivorDomain η J σ Bcap => word p n) := by
  apply measurable_to_countable'
  intro w
  change MeasurableSet {p : eraSurvivorDomain η J σ Bcap | word p n = w}
  by_cases hw : w.length = n
  · have heq : {p : eraSurvivorDomain η J σ Bcap | word p n = w} =
        Subtype.val ⁻¹' eraPrefixDomain η J σ Bcap w := by
      ext p
      exact word_eq_iff p hw
    rw [heq]
    exact (eraPrefixDomain_measurable H w).1.preimage measurable_subtype_coe
  · have heq : {p : eraSurvivorDomain η J σ Bcap | word p n = w} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hw (hp ▸ word_length p n)
    rw [heq]
    exact MeasurableSet.empty

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))
include H

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_measurable :
    Measurable (budgetState (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  choose f hf heq using fun w : List ℕ+ =>
    (MeasurableEmbedding.subtype_coe (eraPrefixDomain_measurable H w).1).exists_measurable_extend
      (eraPrefixDomain_measurable H w).2 (fun _ => inferInstance)
  have hm : Measurable (fun v : List ℕ+ × (ℝ × CoreAngleState) => f v.1 v.2) :=
    measurable_from_prod_countable_right hf
  apply measurable_pi_lambda
  intro n
  have hcomp := hm.comp ((word_measurable H n).prodMk measurable_subtype_coe)
  convert hcomp using 1
  funext p
  exact (congrFun (heq (word p n)) ⟨p.val, mem_word_domain p n⟩).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))
include H
variable (HT : ∀ m : ℕ, ∀ p ∈ eraSelectedInputs η J σ Bcap m,
  ContDiffAt ℝ 1 (eraReturnTime η J m) p.2)
include HT

private theorem BianchiIX.EraSurvivor.duration_measurable :
    Measurable (duration (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  have hm (m : ℕ) : Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraReturnTime η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (HT m p.val p.property).continuousAt)
  choose f hf heq using fun m : ℕ =>
    (MeasurableEmbedding.subtype_coe (H m).1).exists_measurable_extend (hm m) (fun _ => inferInstance)
  have hjoint : Measurable (fun v : ℕ × (ℝ × CoreAngleState) => f v.1 v.2) :=
    measurable_from_prod_countable_right hf
  apply measurable_pi_lambda
  intro n
  have hd : Measurable (fun p : eraSurvivorDomain η J σ Bcap => (digits p n).natPred) :=
    (measurable_of_countable (fun a : ℕ+ => a.natPred)).comp
      ((measurable_pi_apply n).comp (digits_measurable H))
  have hstate := (measurable_pi_apply n).comp (budgetState_measurable H)
  have hcomp := hjoint.comp (hd.prodMk hstate)
  convert hcomp using 1
  funext p
  exact (congrFun (heq (digits p n).natPred) ⟨budgetState p n, budgetState_mem_selected p n⟩).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))
include H
variable (HT : ∀ m : ℕ, ∀ p ∈ eraSelectedInputs η J σ Bcap m,
  ContDiffAt ℝ 1 (eraReturnTime η J m) p.2)
include HT

private theorem BianchiIX.EraSurvivor.elapsedTime_measurable :
    Measurable (elapsedTime (η := η) (J := J) (σ := σ) (Bcap := Bcap)) := by
  apply measurable_pi_lambda
  intro n
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).comp (duration_measurable H HT))

end
end

noncomputable section
open BianchiIX
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}
variable (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
  Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val))
include H
variable (HT : ∀ m : ℕ, ∀ p ∈ eraSelectedInputs η J σ Bcap m,
  ContDiffAt ℝ 1 (eraReturnTime η J m) p.2)
include HT



theorem solution :
    Measurable (fun v : CoreRestartData × eraSurvivorDomain η J σ Bcap => physicalTime v.1 v.2) := by
  apply measurable_pi_lambda
  intro n
  exact (((measurable_pi_apply n).comp (elapsedTime_measurable H HT)).comp measurable_snd).add
    measurable_fst.fst.snd

-- Prove2me | solution 1 for BianchiIX.CoreRestartWitness.restrict_cap
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:33:17.788056+00:00
-- url     : https://prove2.me/submissions/fd47c5f8-286e-4ac0-824f-ea6bef469fec

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

noncomputable section
open BianchiIX

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
open Set
open EraSurvivor

private theorem BianchiIX.EraSurvivor.phase_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) : phase p = phase q := by
  funext n
  unfold phase
  rw [word_eq_of_val p q hpq n, hpq]

end
end


theorem solution {η σ B₁ B₂ : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (H : CoreRestartWitness η J σ B₁ x w)
    (hone : w.2.1 ≤ 1) (hB : w.2.1 ≤ B₂) : CoreRestartWitness η J σ B₂ x w := by
  obtain ⟨ht, hdom, p, hp, hstat, ho⟩ := H
  let q : eraSurvivorDomain η J σ B₂ := ⟨p.val,
    eraSurvivorDomain_restrict_cap p.property (by simpa only [hp] using hone) (by simpa only [hp] using hB)⟩
  refine ⟨ht, hdom, q, hp, ?_, ho⟩
  rw [← EraSurvivor.digits_eq_of_val p q rfl, ← EraSurvivor.phase_eq_of_val p q rfl]
  exact hstat

-- Prove2me | solution 1 for BianchiIX.exists_era_survivor_events
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:39:48.892709+00:00
-- url     : https://prove2.me/submissions/a9ab9cb9-57fd-441e-a070-a8fa60e3f5da

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Theorems.Thm_BianchiIX_exists_era_event_itinerary
import Theorems.Thm_BianchiIX_exists_era_input_avoidance
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
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

private theorem BianchiIX.exists_era_input_event_itinerary :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bcap m, EraEventItinerary η J m p.2 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_event_itinerary
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, C, hC, HE⟩ := Hδ η hη hηδ J (by omega)
  obtain ⟨Bstar, hBstar, hBone, HB⟩ := exists_retained_era_parameter_budget hε
    (le_trans zero_le_one hC) hσ hσone hσJ
  refine ⟨Bstar, hBstar, hBone, ?_⟩
  intro Bcap hcap m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB p.1 ⟨hB.1, hB.2.trans hcap⟩
  have hm' : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBr : p.1 * p.2 0 ≤ ε :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hm')
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ ε / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr)
  exact HE m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
    ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
    (hsum.trans hsmall) ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.eraPrefixState_append (η : ℝ) (J : ℕ) (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    eraPrefixState η J (v ++ w) p = eraPrefixState η J w (eraPrefixState η J v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih => exact ih _

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
open Set MeasureTheory
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

attribute [local instance] BianchiIX.instMeasurableSpaceListPNat_bianchiIX
private theorem BianchiIX.EraSurvivor.budgetState_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    budgetState p (n + 1) = eraBudgetReturn η J (digits p n).natPred (budgetState p n) := by
  unfold budgetState
  rw [word_succ, eraPrefixState_append]
  rfl

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
open BianchiIX.EraSurvivor
variable {η σ Bcap : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.state_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    state p (n + 1) = eraNextState η J (digits p n).natPred (state p n) :=
  congrArg Prod.snd (budgetState_succ p n)

end
end


/-- Every block of every retained infinite history follows the actual core and connection event rules. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap, ∀ n,
            EraEventItinerary η J (EraSurvivor.digits p n).natPred (EraSurvivor.state p n) ∧
              coreRadiusEntry (EraSurvivor.state p (n + 1)) =
                terminalNaturalState η J (eraCoreExit (EraSurvivor.digits p n).natPred (EraSurvivor.state p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_event_itinerary
  obtain ⟨δA, hδA, _, HA⟩ := exists_era_input_avoidance
  refine ⟨min δ δA, lt_min hδ hδA, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BA, hBA, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  refine ⟨min Bstar BA, lt_min hB hBA, (min_le_left _ _).trans_lt hBone, ?_⟩
  intro Bcap hcap p n
  have hinput := (EraSurvivor.budgetState_mem_selected p n).1
  refine ⟨HB Bcap (hcap.trans (min_le_left _ _)) (EraSurvivor.digits p n).natPred
    (EraSurvivor.budgetState p n) hinput, ?_⟩
  have hinA : EraSurvivor.budgetState p n ∈ eraInputSelection σ BA (EraSurvivor.digits p n).natPred :=
    ⟨⟨hinput.1.1, hinput.1.2.trans (hcap.trans (min_le_right _ _))⟩, hinput.2⟩
  obtain ⟨_, _, _, _, hrec, _⟩ := Ha (EraSurvivor.digits p n).natPred (EraSurvivor.budgetState p n) hinA
  rw [EraSurvivor.state_succ]
  exact hrec

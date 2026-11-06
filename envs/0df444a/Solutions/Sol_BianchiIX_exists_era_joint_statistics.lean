-- Prove2me | solution 1 for BianchiIX.exists_era_joint_statistics
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:48:07.354+00:00
-- url     : https://prove2.me/submissions/08479ecd-810c-4aa7-89fc-6db5853b026a

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
import Definitions.Def_BianchiIX_Statistics_TreeDistortion
import Definitions.Def_BianchiIX_Statistics_TreeOrbits
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_Statistics_EraBudget
import Definitions.Def_BianchiIX_EraCodingData
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_terminal_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_BranchEstimates_typicalSurvivors_era_bounds
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_append
import Theorems.Thm_BianchiIX_InverseBranchTree_cell_nil
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_level
import Theorems.Thm_BianchiIX_InverseBranchTree_mem_typicalSurvivors
import Theorems.Thm_BianchiIX_InverseBranchTree_phase_mem_terminal
import Theorems.Thm_BianchiIX_InverseBranchTree_survivors_subset_root
import Theorems.Thm_BianchiIX_InverseBranchTree_terminal_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_append
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_nil
import Theorems.Thm_BianchiIX_InverseBranchTree_toRoot_phase
import Theorems.Thm_BianchiIX_InverseBranchTree_typicalSurvivors_measurable
import Theorems.Thm_BianchiIX_InverseBranchTree_typicalSurvivors_subset
import Theorems.Thm_BianchiIX_InverseBranchTree_word_succ
import Theorems.Thm_BianchiIX_eraAmplitude_le
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_succ
import Theorems.Thm_BianchiIX_eraAmplitude_zero
import Theorems.Thm_BianchiIX_exists_era_budget_threshold
import Theorems.Thm_BianchiIX_exists_era_curve_step
import Theorems.Thm_BianchiIX_exists_era_output_estimates
import Theorems.Thm_BianchiIX_exists_era_selected_inputs_inverse
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_gaussCylinderTypicalSet_measurable
import Theorems.Thm_BianchiIX_measurable_gaussCode
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
open Set MeasureTheory
open scoped ENNReal

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
open EraCurve

private theorem BianchiIX.EraCurve.constant_admissible {B : ℝ} (hB : 0 < B) : (constant B).Admissible B := by
  intro r _
  refine ⟨half_pos hB, half_pos hB, by dsimp [constant]; linarith,
    contDiffAt_const, contDiffAt_const, ?_, ?_⟩ <;>
    simpa only [constant, deriv_const, abs_zero] using Real.sqrt_nonneg (B / 2)

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

@[simp] private theorem BianchiIX.EraCurve.family_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) :
    Γ.family η J σ B [] = Γ := by simp [family, List.reverseRecOn]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

@[simp] private theorem BianchiIX.EraCurve.family_append (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) (a : ℕ+) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).nextCurve η J σ (eraAmplitude B w.length) a := by
  simp [family, List.reverseRecOn]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.EraCurve.family_append_of_retained (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ)
    (w : List ℕ+) (a : ℕ+) (ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).successor η J a.natPred ((eraAmplitude B w.length) ^ σ) := by
  rw [family_append, nextCurve, if_pos ha]

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.EraCurve.family_admissible {η σ B Bstar C : ℝ} {J : ℕ} {Γ : EraCurve}
    (hB : B ∈ Ioc 0 Bstar) (hBs : Bstar ≤ 1) (hΓ : Γ.Admissible B)
    (H : ∀ b ∈ Ioc 0 Bstar, ∀ γ : EraCurve, γ.Admissible b → γ.StepEstimates η J σ b C)
    (w : List ℕ+) : (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) := by
  have hb (n : ℕ) : eraAmplitude B n ∈ Ioc 0 Bstar :=
    ⟨eraAmplitude_pos hB.1 n, (eraAmplitude_le hB.1.le (hB.2.trans hBs) n).trans hB.2⟩
  induction w using List.reverseRecOn with
  | nil => simpa using hΓ
  | append_singleton w a ih =>
    rw [family_append, List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    unfold nextCurve
    split_ifs with ha
    · exact (H _ (hb w.length) _ ih).successor_admissible a.natPred ha
    · exact constant_admissible (Real.rpow_pos_of_pos (hb w.length).1 _)

end
end

section
noncomputable section
open BianchiIX
open Set
open EraCurve

private theorem BianchiIX.exists_era_curve_family :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B → ∀ w : List ℕ+,
            (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
            (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_curve_step
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bs, hBs, hBsone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨C, hC, Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ w
  have ha := EraCurve.family_admissible hB hBsone.le hΓ H w
  exact ⟨ha, H _ ⟨eraAmplitude_pos hB.1 _,
    (eraAmplitude_le hB.1.le (hB.2.trans hBsone.le) _).trans hB.2⟩ _ ha⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_eraInputSelection {σ : ℝ} (hσ : 0 ≤ σ) (Bstar : ℝ) (m : ℕ) :
    MeasurableSet (eraInputSelection σ Bstar m) := by
  have hβ : Measurable (fun p : ℝ × CoreAngleState => p.1 ^ σ) :=
    (Real.continuous_rpow_const hσ).measurable.comp measurable_fst
  have hx (i : Fin 3) : Measurable (fun p : ℝ × CoreAngleState => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const (measurable_const.div hβ).nat_floor).inter
      ((measurableSet_lt measurable_const (hx 1)).inter
        ((measurableSet_lt measurable_const (hx 2)).inter
          ((measurableSet_le ((hx 1).add (hx 2)) measurable_fst).inter
            ((measurableSet_le ((measurable_const.add hβ).const_mul 2) (hx 0)).inter
              (measurableSet_le (hx 0) ((measurable_const.sub hβ).const_mul 2)))))))

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

private theorem BianchiIX.eraSelectedInputs_measurable_of_contDiff {η σ Bstar : ℝ} {J m : ℕ} (hσ : 0 ≤ σ)
    (H : ∀ p ∈ eraInputSelection σ Bstar m, ContDiffAt ℝ 1 (eraNextState η J m) p.2) :
    MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val) := by
  let D := eraInputSelection σ Bstar m
  have hD : MeasurableSet D := measurableSet_eraInputSelection hσ Bstar m
  have hstate : Measurable (fun p : D => eraNextState η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (H p.val p.property).continuousAt)
  have hphase : Measurable (fun p : D => 2 / eraOutputRadius η J m p.val.2) :=
    measurable_const.div ((measurable_pi_apply 0).comp hstate)
  have hβ : Measurable (fun p : D => p.val.1 ^ σ) :=
    (Real.continuous_rpow_const hσ).measurable.comp (measurable_fst.comp measurable_subtype_coe)
  have hs : MeasurableSet {p : D | 2 / eraOutputRadius η J m p.val.2 ∈
      Ioo (2 * p.val.1 ^ σ) (1 - 2 * p.val.1 ^ σ)} :=
    (measurableSet_lt (hβ.const_mul 2) hphase).inter
      (measurableSet_lt hphase (measurable_const.sub (hβ.const_mul 2)))
  have heq : eraSelectedInputs η J σ Bstar m =
      Subtype.val '' {p : D | 2 / eraOutputRadius η J m p.val.2 ∈
        Ioo (2 * p.val.1 ^ σ) (1 - 2 * p.val.1 ^ σ)} := by
    ext p
    constructor
    · exact fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
  refine ⟨by rw [heq]; exact hD.subtype_image hs, ?_⟩
  have hnext : Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraNextState η J m p.val.2) :=
    measurable_comp_of_continuousAt (measurable_snd.comp measurable_subtype_coe)
      (fun p => (H p.val p.property.1).continuousAt)
  change Measurable (fun p : eraSelectedInputs η J σ Bstar m =>
    (p.val.1 ^ (4 / 3 : ℝ), eraNextState η J m p.val.2))
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4 / 3)).measurable.comp
    (measurable_fst.comp measurable_subtype_coe)).prodMk hnext

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_era_selected_inputs_measurable :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ,
          (∀ p ∈ eraInputSelection σ Bstar m, ContDiffAt ℝ 1 (eraNextState η J m) p.2) ∧
          MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
          Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_output_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, Hout⟩ := Hδ η hη hηδ J hJ
  obtain ⟨Bs, hBs, hBsone, Hbudget⟩ :=
    exists_retained_era_parameter_budget hε (by linarith : 0 ≤ C) hσ hσone hσJ
  refine ⟨Bs, hBs, hBsone, ?_⟩
  intro m
  have Hactual : ∀ p ∈ eraInputSelection σ Bs m, ContDiffAt ℝ 1 (eraNextState η J m) p.2 := by
    intro p hp
    obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
    obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hbudget p.1 hB
    have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
      (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
        (Nat.floor_le (by positivity))
    have hrpos : 0 < p.2 0 := by nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m]
    have hBr : p.1 * p.2 0 ≤ ε :=
      (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
    have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ ε / p.2 0 :=
      (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr)
    obtain ⟨HS, HR, _⟩ := Hout m (p.1 ^ σ) p.2 hβ (by linarith)
      ⟨hu, hwall (by linarith)⟩ ⟨hw, hwall (by linarith)⟩ (hsum.trans hsmall)
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
      ((mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ C)).trans_lt hmargin)
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact HR
    · exact contDiffAt_pi.mp HS 1
    · exact contDiffAt_pi.mp HS 3
  exact ⟨Hactual, eraSelectedInputs_measurable_of_contDiff hσ.le Hactual⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.inverseTree_estimates {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    (Γ.inverseTree η J σ B C H).BranchEstimates (fun n => C * eraAmplitude B n)
      (fun n => 5 * C * Real.sqrt (eraAmplitude B n)) := by
  refine ⟨Subset.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro w a y hy
    obtain ⟨_, hy⟩ := mem_eraTreeDomain.mp hy
    exact ⟨by linarith [(H w).beta_pos, hy.1], by linarith [(H w).beta_pos, hy.2]⟩
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.1.differentiableAt (by norm_num)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    exact (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.1.ne
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hv := (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.1
    have hden : 1 ≤ ((a.natPred : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) a.natPred]
    have hb : 0 ≤ C * eraAmplitude B w.length := mul_nonneg hC (eraAmplitude_pos hB _).le
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using hv.trans (div_le_self hb hden)
  · intro w a y hy
    obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
    have hcast : (a.natPred : ℝ) + 1 = (a : ℝ) := by exact_mod_cast a.natPred_add_one
    simpa only [inverseTree, treeBranch, hcast] using (((H w).branch a.natPred ha).2 y ⟨hy.1.le, hy.2.le⟩).2.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.treeBranch_union {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ} (w : List ℕ+)
    (H : (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C) :
    (⋃ a : ℕ+, Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a) =
      eraRetainedPhases η J ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ ((eraAmplitude B w.length) ^ σ)
        (Γ.family η J σ B w).U (Γ.family η J σ B w).W := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx
    have hret : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊ := by
      obtain ⟨y, hy, _⟩ := ha
      exact (mem_eraTreeDomain.mp hy).1
    rw [treeBranch_image_of_retained H a hret] at ha
    exact mem_iUnion₂.mpr ⟨a.natPred, Finset.mem_range.mpr hret, ha⟩
  · intro hx
    obtain ⟨m, hm, hxI⟩ := mem_iUnion₂.mp hx
    let a : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    have ha : a.natPred = m := by simp [a, PNat.natPred]
    apply mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [treeBranch_image_of_retained H a (by simpa [ha] using Finset.mem_range.mp hm)]
    simpa only [treeBranch, ha] using hxI

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.inverseTree_stopped_volume {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (hB : 0 < B) (hC : 0 ≤ C)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (w : List ℕ+) :
    volume ((Γ.inverseTree η J σ B C H).stoppedDomain w) ≤
      ENNReal.ofReal (10 * (eraAmplitude B w.length) ^ σ) := by
  have hterminal := (inverseTree_estimates hB hC H).terminal_subset w
  have hsub : (Γ.inverseTree η J σ B C H).stoppedDomain w ⊆
      Ioo (0 : ℝ) 1 \ eraRetainedPhases η J ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
        ((eraAmplitude B w.length) ^ σ) (Γ.family η J σ B w).U (Γ.family η J σ B w).W := by
    intro x hx
    refine ⟨hterminal hx.1, ?_⟩
    rw [← treeBranch_union w (H w)]
    exact hx.2
  exact (measure_mono hsub).trans (H w).stopped_volume

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open EraCurve

private theorem BianchiIX.EraCurve.inverseTree_successor_match {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (w : List ℕ+) (a : ℕ+) (y : ℝ)
    (hy : y ∈ (Γ.inverseTree η J σ B C H).domain w a) :
    let x := 2 / (Γ.inverseTree η J σ B C H).branch w a y
    let X := (Γ.family η J σ B w).state x
    eraOutputRadius η J a.natPred X = 2 / y ∧
      (Γ.family η J σ B (w ++ [a])).U (2 / y) = eraOutputState η J a.natPred X 1 ∧
      (Γ.family η J σ B (w ++ [a])).W (2 / y) = eraOutputState η J a.natPred X 3 := by
  obtain ⟨ha, hy⟩ := mem_eraTreeDomain.mp hy
  have hm := (H w).successor_match a.natPred ha y ⟨hy.1.le, hy.2.le⟩
  dsimp only
  rw [family_append_of_retained Γ η J σ B w a ha]
  exact hm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_era_selected_return :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          (∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
            Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B →
            ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ x : ℝ,
              (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bstar m ↔
                x ∈ eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := by
  obtain ⟨δm, hδm, hδmax, HM⟩ := exists_era_selected_inputs_measurable
  obtain ⟨δi, hδi, _, HI⟩ := exists_era_selected_inputs_inverse
  refine ⟨min δm δi, lt_min hδm hδi, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bm, hBm, hBmone, Hm⟩ := HM η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bi, hBi, _, Hi⟩ := HI η hη (hηδ.trans (min_le_right _ _)) J (by omega) σ hσ hσone hσJ
  refine ⟨min Bm Bi, lt_min hBm hBi, (min_le_left _ _).trans_lt hBmone, ?_, ?_⟩
  · intro m
    apply eraSelectedInputs_measurable_of_contDiff hσ.le
    intro p hp
    exact (Hm m).1 p ⟨⟨hp.1.1, hp.1.2.trans (min_le_left _ _)⟩, hp.2⟩
  · intro B hB Γ hΓ m hm x
    have hBi' : B ∈ Ioc 0 Bi := ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
    have heq : (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ (min Bm Bi) m ↔
        (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bi m := by
      simp only [eraSelectedInputs, eraInputSelection, mem_ofPred_eq, hB, hBi', true_and]
    exact heq.trans (Hi B hBi' Γ hΓ m hm x)

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

private theorem BianchiIX.eraSurvivorDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (eraSurvivorDomain η J σ Bstar) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w => (eraPrefixDomain_measurable H w.val).1

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
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.code_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (code (η := η) (J := J) (σ := σ) (Bstar := Bstar)) :=
  measurable_gaussCode.comp (digits_measurable H)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.typicalDomain_subset : typicalDomain η J σ Bstar ⊆ eraSurvivorDomain η J σ Bstar := by
  rintro _ ⟨p, _, rfl⟩
  exact p.property

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.mem_typicalDomain (p : eraSurvivorDomain η J σ Bstar) :
    p.val ∈ typicalDomain η J σ Bstar ↔ code p ∈ gaussCylinderTypicalSet := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hp : q = p := Subtype.ext heq
    simpa only [hp, mem_ofPred_eq] using hq
  · exact fun hp => ⟨p, hp, rfl⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraSurvivor
variable {η σ Bstar : ℝ} {J : ℕ}

private theorem BianchiIX.EraSurvivor.typicalDomain_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (typicalDomain η J σ Bstar) :=
  (eraSurvivorDomain_measurable H).subtype_image
    (gaussCylinderTypicalSet_measurable.preimage (code_measurable H))

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve

@[simp] private theorem BianchiIX.EraCurve.treeState_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B x : ℝ) :
    Γ.treeState η J σ B [] x = (B, Γ.state (2 / x)) := by simp [treeState]

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve

private theorem BianchiIX.EraCurve.realization_of_estimates {Γ : EraCurve} {η σ B Bcap C : ℝ} {J : ℕ}
    (hB : B ∈ Ioc 0 Bcap) (hcap : Bcap ≤ 1)
    (H : ∀ w : List ℕ+, (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
      (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C)
    (Hselect : ∀ b ∈ Ioc 0 Bcap, ∀ γ : EraCurve, γ.Admissible b →
      ∀ m : ℕ, m < ⌊1 / b ^ σ⌋₊ → ∀ x : ℝ,
        (b, γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bcap m ↔
          x ∈ eraInverseBranch η J m (b ^ σ) γ.U γ.W '' Ioo (2 * b ^ σ) (1 - 2 * b ^ σ)) :
    Γ.Realization η J σ B Bcap (Γ.inverseTree η J σ B C (fun w => (H w).2)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w a y hy
    have hm := inverseTree_successor_match (fun w => (H w).2) w a y hy
    apply Prod.ext
    · change (eraAmplitude B w.length) ^ (4 / 3 : ℝ) = eraAmplitude B (w ++ [a]).length
      rw [List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    · funext i
      fin_cases i
      · exact hm.1
      · exact hm.2.1.symm
      · exact hm.2.2.symm
  · intro w a x
    have hb : eraAmplitude B w.length ∈ Ioc 0 Bcap :=
      ⟨eraAmplitude_pos hB.1 _, (eraAmplitude_le hB.1.le (hB.2.trans hcap) _).trans hB.2⟩
    by_cases ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊
    · change (eraAmplitude B w.length, (Γ.family η J σ B w).state (2 / x)) ∈ _ ↔
        x ∈ Γ.treeBranch η J σ B w a '' eraTreeDomain σ B w a
      rw [eraTreeDomain, if_pos ha]
      exact Hselect _ hb _ (H w).1 a.natPred ha x
    · have hd : (Γ.inverseTree η J σ B C (fun w => (H w).2)).domain w a = ∅ := by
        change eraTreeDomain σ B w a = ∅
        rw [eraTreeDomain, if_neg ha]
      rw [hd, image_empty, mem_empty_iff_false, iff_false]
      exact fun hx => ha hx.1.2.1

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.prefix_state (w : List ℕ+) (y : ℝ) (hy : y ∈ T.terminal w) :
    eraPrefixState η J w (B, Γ.state (2 / T.toRoot w y)) = Γ.treeState η J σ B w y := by
  induction w using List.reverseRecOn generalizing y with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [T.terminal_append] at hy
    rw [eraPrefixState_append, T.toRoot_append]
    change eraBudgetReturn η J a.natPred
      (eraPrefixState η J w (B, Γ.state (2 / T.toRoot w (T.branch w a y)))) = _
    rw [ih _ hy.2]
    exact R.step w a y hy.1

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.prefix_domain_iff_cell (w : List ℕ+) (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraPrefixDomain η J σ Bcap w ↔ x ∈ T.cell w := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixDomain, hx]
  | append_singleton w a ih =>
    rw [mem_eraPrefixDomain_append, T.cell_append]
    simp only [eraPrefixDomain, mem_inter_iff, mem_preimage, mem_univ, and_true]
    constructor
    · rintro ⟨hp, hnext⟩
      obtain ⟨z, hz, hzx⟩ := ih.mp hp
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs] at hnext
      exact ⟨z, ⟨hz, (R.selected w a z).mp hnext⟩, hzx⟩
    · rintro ⟨z, ⟨hz, hnext⟩, hzx⟩
      refine ⟨ih.mpr ⟨z, hz, hzx⟩, ?_⟩
      have hs := R.prefix_state w z hz
      rw [hzx] at hs
      rw [hs]
      exact (R.selected w a z).mpr hnext

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.survivor_iff (x : ℝ) (hx : x ∈ T.root) :
    (B, Γ.state (2 / x)) ∈ eraSurvivorDomain η J σ Bcap ↔ x ∈ T.survivors := by
  constructor
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
    exact T.mem_level.mpr ⟨w.val, w.property, (R.prefix_domain_iff_cell w.val x hx).mp hw⟩
  · intro hp
    apply mem_iInter.mpr
    intro n
    obtain ⟨w, hw, hc⟩ := T.mem_level.mp (mem_iInter.mp hp n)
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, (R.prefix_domain_iff_cell w x hx).mpr hc⟩

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.word_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) (n : ℕ) : EraSurvivor.word p n = T.word x n := by
  apply (EraSurvivor.word_eq_iff p (T.word_length x n)).mpr
  rw [hp]
  exact (R.prefix_domain_iff_cell _ _ (T.survivors_subset_root x.property)).mpr (T.mem_word_cell x n)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.digits_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.digits p = T.digits x := by
  funext n
  have heq := (EraSurvivor.word_succ p n).symm.trans
    ((R.word_eq_tree x p hp (n + 1)).trans (T.word_succ x n))
  rw [R.word_eq_tree x p hp n] at heq
  exact List.singleton_inj.mp (List.append_inj_right heq rfl)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.code_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.code p = T.code x := by
  exact congrArg gaussCode (R.digits_eq_tree x p hp)

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.phase_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.phase p = T.phase x := by
  funext n
  unfold EraSurvivor.phase
  rw [R.word_eq_tree x p hp n, hp]
  have hs := R.prefix_state (T.word x n) (T.phase x n) (T.phase_mem_terminal x n)
  rw [T.toRoot_phase] at hs
  rw [hs]
  change 2 / (2 / T.phase x n) = T.phase x n
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set
open BianchiIX.EraCurve.Realization
variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)
include R

private theorem BianchiIX.EraCurve.Realization.curveTypicalSet_eq : EraSurvivor.curveTypicalSet Γ η J σ B Bcap = T.typicalSurvivors := by
  ext x
  constructor
  · intro hx
    have hxroot : x ∈ T.root := by rw [R.root]; exact hx.1
    have hs := EraSurvivor.typicalDomain_subset hx.2
    let xt : T.survivors := ⟨x, (R.survivor_iff x hxroot).mp hs⟩
    let p : eraSurvivorDomain η J σ Bcap := ⟨(B, Γ.state (2 / x)), hs⟩
    apply (T.mem_typicalSurvivors xt).mpr
    rw [← R.code_eq_tree xt p rfl]
    exact (EraSurvivor.mem_typicalDomain p).mp hx.2
  · intro hx
    let xt : T.survivors := ⟨x, T.typicalSurvivors_subset hx⟩
    have hxroot : x ∈ T.root := T.survivors_subset_root xt.property
    let p : eraSurvivorDomain η J σ Bcap := ⟨(B, Γ.state (2 / x)), (R.survivor_iff x hxroot).mpr xt.property⟩
    refine ⟨by rwa [← R.root], ?_⟩
    apply (EraSurvivor.mem_typicalDomain p).mpr
    rw [R.code_eq_tree xt p rfl]
    exact (T.mem_typicalSurvivors xt).mp hx

end
end


/-- One Borel set of actual states supplies the same statistical set and loss bound on every admissible curve. -/
theorem solution (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ MeasurableSet (EraSurvivor.typicalDomain η J σ Bcap) ∧
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
            ∀ Γ : EraCurve, Γ.Admissible B →
              MeasurableSet (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (1 / 2 : ℝ≥0∞) < volume (EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ∧
              (∀ I : Set ℝ, volume ((I ∩ Ioo 0 1) \ (I ∩ EraSurvivor.curveTypicalSet Γ η J σ B Bcap)) ≤
                min (volume I) (ENNReal.ofReal (80 * B ^ σ))) ∧
              ∀ x ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap,
                ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Γ.state (2 / x)) ∧
                  EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δt, hδt, hδmax, HT⟩ := exists_era_curve_family
  obtain ⟨δs, hδs, _, HS⟩ := exists_era_selected_return
  refine ⟨min δt δs, lt_min hδt hδs, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bt, hBt, hBtone, Htree⟩ := HT η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bs, hBs, hBsone, Hmeas, Hselect⟩ := HS η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  have hC0 : 0 ≤ C := by linarith
  have hCi : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC0
  obtain ⟨Bb, hBb, _, Hbudget⟩ :=
    exists_era_budget_threshold hσ hC0 hCi (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨Bs, hBs, hBsone, EraSurvivor.typicalDomain_measurable Hmeas,
    min Bt (min Bs Bb), lt_min hBt (lt_min hBs hBb), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro B hB Γ hΓ
  have hBt' : B ∈ Ioc 0 Bt := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBs' : B ∈ Ioc 0 Bs := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hnodes := Htree B hBt' Γ hΓ
  let T := Γ.inverseTree η J σ B C (fun w => (Hnodes w).2)
  have R : Γ.Realization η J σ B Bs T := EraCurve.realization_of_estimates hBs' hBsone.le Hnodes Hselect
  have E := EraCurve.inverseTree_estimates hB.1 hC0 (fun w => (Hnodes w).2)
  obtain ⟨hsmall, hL, _⟩ := Hbudget B hBb'
  have hJreal : (2 : ℝ) ≤ (2 * J : ℕ) := by exact_mod_cast (show 2 ≤ 2 * J by omega)
  have hσhalf : σ ≤ 1 / 2 := by nlinarith
  have Hstats := E.typicalSurvivors_era_bounds hBirkhoff R.root hB.1 (hBs'.2.trans hBsone.le)
    hσ.le hσhalf hsmall hC0 hCi hL (EraCurve.inverseTree_stopped_volume hB.1 hC0 (fun w => (Hnodes w).2))
  have heq := R.curveTypicalSet_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact T.typicalSurvivors_measurable
  · rw [heq]
    exact Hstats.1
  · intro I
    rw [heq, ← R.root]
    exact Hstats.2.1 I
  · intro x hx
    have ht : x ∈ T.typicalSurvivors := by rwa [← heq]
    let xt : T.survivors := ⟨x, T.typicalSurvivors_subset ht⟩
    let p : eraSurvivorDomain η J σ Bs :=
      ⟨(B, Γ.state (2 / x)), (R.survivor_iff x (T.survivors_subset_root xt.property)).mpr xt.property⟩
    refine ⟨p, rfl, ?_⟩
    rw [R.digits_eq_tree xt p rfl, R.phase_eq_tree xt p rfl]
    exact Hstats.2.2 xt ht

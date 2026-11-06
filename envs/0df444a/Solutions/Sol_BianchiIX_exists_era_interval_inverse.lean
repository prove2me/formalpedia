-- Prove2me | solution 1 for BianchiIX.exists_era_interval_inverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:42:46.402219+00:00
-- url     : https://prove2.me/submissions/67924792-a7bb-4af3-96fa-8ee1c627e6a8

import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_intervalRadiusInverse_positive_control
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

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_scalarLocalInverseAt {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 1 f a) (hd : deriv f a ≠ 0) :
    ∃ g, ScalarLocalInverseAt f a g := by
  have hs := hf.hasStrictDerivAt (by norm_num)
  let g := hs.localInverse f (deriv f a) a hd
  refine ⟨g, ⟨(hs.eventually_left_inverse hd).self_of_nhds, ?_,
    (hs.to_localInverse hd).hasDerivAt, hs.eventually_left_inverse hd, hs.eventually_right_inverse hd⟩⟩
  have HE := hs.hasStrictFDerivAt_equiv hd
  exact hf.to_localInverse HE.hasFDerivAt (by norm_num)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.ScalarLocalInverseAt.deriv_eq {f g : ℝ → ℝ} {a : ℝ}
    (H : ScalarLocalInverseAt f a g) : deriv g (f a) = (deriv f a)⁻¹ := H.hasDerivAt.deriv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.graphPhase_differential {F : (Fin 3 → ℝ) → ℝ} {U W : ℝ → ℝ} {r : ℝ}
    (hF : ContDiffAt ℝ 1 F ![r, U r, W r])
    (hU : ContDiffAt ℝ 1 U r) (hW : ContDiffAt ℝ 1 W r) :
    ContDiffAt ℝ 1 (graphPhase F U W) r ∧
      HasDerivAt (graphPhase F U W)
        (fderiv ℝ F ![r, U r, W r] ![1, deriv U r, deriv W r]) r := by
  let γ := fun t => (![t, U t, W t] : Fin 3 → ℝ)
  have Hγ : ContDiffAt ℝ 1 γ r := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_id
    · exact hU
    · exact hW
  have HDγ : HasDerivAt γ ![1, deriv U r, deriv W r] r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_id r
    · exact (hU.differentiableAt (by norm_num)).hasDerivAt
    · exact (hW.differentiableAt (by norm_num)).hasDerivAt
  exact ⟨hF.comp r Hγ,
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r HDγ⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_era_graph_inverse :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β r : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 2 →
        (0 < U r ∧ U r ≤ ε / r) → (0 < W r ∧ W r ≤ ε / r) →
        U r + W r ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β) →
        C * (U r + W r) < β / 4 →
        ContDiffAt ℝ 1 U r → ContDiffAt ℝ 1 W r →
        |deriv U r| ≤ Real.sqrt (U r) → |deriv W r| ≤ Real.sqrt (W r) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        ContDiffAt ℝ 1 φ r ∧ (β / 2 < φ r ∧ φ r < 1 - β / 2) ∧
        |φ r - (r / 2 - ((m : ℝ) + 1))| ≤ C * (U r + W r) ∧
        0 < deriv φ r ∧ |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt (U r + W r) ∧
        ∃ g, ScalarLocalInverseAt φ r g ∧ 0 < deriv g (φ r) ∧
          |Real.log (deriv g (φ r) / 2)| ≤ C * Real.sqrt (U r + W r) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_bounded_phase_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β r U W hβ hβmax hu hw hsmall hphase hmargin hU hW hdU hdW φ
  obtain ⟨_, HP, _, _, hwindow, hvalue, _, _, _, _, _, _, _, _, _, _, HD⟩ :=
    HE m β ![r, U r, W r] hβ hβmax hu hw hsmall hphase hmargin
  obtain ⟨Hφ, Hder⟩ := graphPhase_differential HP hU hW
  have Hdir := HD ![1, deriv U r, deriv W r] rfl hdU hdW
  have hpos : 0 < deriv φ r := by rw [Hder.deriv]; exact Hdir.1
  have hlog : |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt (U r + W r) := by
    rw [Hder.deriv]
    exact Hdir.2
  obtain ⟨g, Hg⟩ := exists_scalarLocalInverseAt Hφ hpos.ne'
  refine ⟨Hφ, hwindow, hvalue, hpos, hlog, g, Hg, ?_, ?_⟩
  · rw [Hg.deriv_eq]
    exact inv_pos.mpr hpos
  · rw [Hg.deriv_eq, show (deriv φ r)⁻¹ / 2 = (2 * deriv φ r)⁻¹ by ring,
      Real.log_inv, abs_neg]
    exact hlog

end
end


/-- Actual era graphs cover the same output interval, with a unique C1 radius inverse there. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        let g := intervalRadiusInverse φ a b
        StrictMonoOn φ (Icc a b) ∧ LeftInvOn g φ (Icc a b) ∧
        φ a < 2 * β ∧ 1 - 2 * β < φ b ∧
        ∀ y ∈ Icc (2 * β) (1 - 2 * β),
          g y ∈ Ioo a b ∧ φ (g y) = y ∧
          (∀ r ∈ Icc a b, φ r = y → r = g y) ∧
          ContDiffAt ℝ 1 g y ∧ HasDerivAt g (deriv φ (g y))⁻¹ y ∧
          0 < deriv g y ∧ |g y / 2 - ((m : ℝ) + 1 + y)| ≤ C * B ∧
          |Real.log (deriv g y / 2)| ≤ C * Real.sqrt B := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_graph_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph φ g
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hab : a < b := by dsimp [a, b]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 < B := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph a ⟨le_rfl, hab.le⟩
    linarith
  have hC0 : 0 ≤ C := by linarith
  have Hφ (r : ℝ) (hr : r ∈ Icc a b) :
      ContDiffAt ℝ 1 φ r ∧ |φ r - (r / 2 - ((m : ℝ) + 1))| ≤ C * B ∧
      0 < deriv φ r ∧ |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt B := by
    obtain ⟨hu, hw, hsum, hU, hW, hdU, hdW⟩ := Hgraph r hr
    have hr0 := ha.trans_le hr.1
    have hBr : B * r ≤ ε := (mul_le_mul_of_nonneg_left hr.2 hB.le).trans hscale
    have huε : U r ≤ ε / r := (le_div_iff₀ hr0).mpr (by
      exact (mul_le_mul_of_nonneg_right (by linarith : U r ≤ B) hr0.le).trans hBr)
    have hwε : W r ≤ ε / r := (le_div_iff₀ hr0).mpr (by
      exact (mul_le_mul_of_nonneg_right (by linarith : W r ≤ B) hr0.le).trans hBr)
    have hphase : (m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β := by
      dsimp [a, b] at hr
      constructor <;> linarith [hr.1, hr.2]
    have herror := mul_le_mul_of_nonneg_left hsum hC0
    obtain ⟨hf, _, hv, hd, hl, _⟩ := HE m β r U W hβ (by linarith)
      ⟨hu, huε⟩ ⟨hw, hwε⟩ (hsum.trans hsmall) hphase (herror.trans_lt hmargin)
      hU hW hdU hdW
    exact ⟨hf, hv.trans herror, hd,
      hl.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) hC0)⟩
  obtain ⟨hmono, _, hleft, _, hright, Hinv⟩ :=
    intervalRadiusInverse_positive_control hab (fun r hr => (Hφ r hr).1)
      (fun r hr => (Hφ r hr).2.2.1)
  have hfa : φ a < 2 * β := by
    have hv := (abs_le.mp (Hφ a ⟨le_rfl, hab.le⟩).2.1).2
    dsimp [a] at hv
    linarith
  have hfb : 1 - 2 * β < φ b := by
    have hv := (abs_le.mp (Hφ b ⟨hab.le, le_rfl⟩).2.1).1
    dsimp [b] at hv
    linarith
  refine ⟨hmono, hleft, hfa, hfb, ?_⟩
  intro y hy
  have hyi : y ∈ Ioo (φ a) (φ b) := ⟨hfa.trans_le hy.1, hy.2.trans_lt hfb⟩
  obtain ⟨hgi, hg, hgd⟩ := Hinv y hyi
  have hgc : g y ∈ Icc a b := ⟨hgi.1.le, hgi.2.le⟩
  have hfg : φ (g y) = y := hright ⟨hyi.1.le, hyi.2.le⟩
  have Hpoint := Hφ (g y) hgc
  refine ⟨hgi, hfg, ?_, hg, hgd, ?_, ?_, ?_⟩
  · intro r hr hfy
    exact hmono.injOn hr hgc (hfy.trans hfg.symm)
  · rw [hgd.deriv]
    exact inv_pos.mpr Hpoint.2.2.1
  · have hv := Hpoint.2.1
    rw [hfg] at hv
    rw [show g y / 2 - ((m : ℝ) + 1 + y) =
      -(y - (g y / 2 - ((m : ℝ) + 1))) by ring, abs_neg]
    exact hv
  · rw [hgd.deriv, show (deriv φ (g y))⁻¹ / 2 = (2 * deriv φ (g y))⁻¹ by ring,
      Real.log_inv, abs_neg]
    exact Hpoint.2.2.2

-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_connection_curve
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:05:34.459938+00:00
-- url     : https://prove2.me/submissions/b20026e8-10fd-44a5-81d7-add6b889a76f

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_coreExit_curve
import Theorems.Thm_BianchiIX_exists_restartShearTail_connection
import Theorems.Thm_BianchiIX_exists_restartShearTail_core_cone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_curve_derivative_pos {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hf0 : f x ≠ 0) (hdf : deriv f x < 0) :
    0 < deriv (fun a => 2 / f a) x := by
  have H : HasDerivAt (fun a => 2 / f a) (-2 * deriv f x / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf.hasDerivAt hf0 using 1
    ring
  rw [H.deriv]
  exact div_pos (by linarith only [hdf]) (sq_pos_of_ne_zero hf0)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_curve_identities {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) (hdf : deriv f x ≠ 0) :
    DifferentiableAt ℝ (fun a => 2 / f a) x ∧
      DifferentiableAt ℝ (fun a => 2 / g a) x ∧
      2 / g x - 2 / f x = -2 * (g x - f x) / (f x * g x) ∧
      deriv (fun a => 2 / g a) x / deriv (fun a => 2 / f a) x =
        (f x / g x) ^ 2 * (deriv g x / deriv f x) := by
  have Hf : HasDerivAt (fun a => 2 / f a) (-2 * deriv f x / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf.hasDerivAt hf0 using 1
    ring
  have Hg : HasDerivAt (fun a => 2 / g a) (-2 * deriv g x / (g x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hg.hasDerivAt hg0 using 1
    ring
  refine ⟨Hf.differentiableAt, Hg.differentiableAt, ?_, ?_⟩
  · field_simp
    ring
  · rw [Hf.deriv, Hg.deriv]
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_connection_cone_threshold :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ Real.sqrt ε ≤ 1 / 1000000 ∧ ε ≤ Real.exp (-256) := by
  let ε := min ((1 / 1000000 : ℝ) ^ 2) (Real.exp (-256))
  have hε0 : 0 < ε := lt_min (by norm_num) (Real.exp_pos _)
  have hεd : ε ≤ (1 / 1000000 : ℝ) ^ 2 := min_le_left _ _
  refine ⟨ε, hε0, ?_, ?_, min_le_right _ _⟩
  · exact hεd.trans (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hεd]⟩

end
end

/-- The long-tail return preserves the square-root cone and both ordinary reciprocal-phase identities through its connection. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
          let f := fun r => partialCoreDownwardReturnState (Y r) 0
          let p := restartShearReturnParameters h s ζ ν
          let G := restartShearReturnState h s ζ ν
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ DifferentiableAt ℝ f ρ ∧
          1 < f ρ ∧ 0 < g ρ ∧ deriv f ρ < 0 ∧ deriv g ρ < 0 ∧
          |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
          (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
          (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
          DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧ DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
          (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
          2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
          deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
            (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_core_cone
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_connection
  obtain ⟨η, hη0, hη, hsη, hηL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP η ⟨hη0, hη⟩
  refine ⟨min aC aE, lt_min haC haE, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s Y f p G g
  obtain ⟨hκ, _, HZ, _, hdf, _, _, Hcone⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, hμ, hU, hW, _, _, hf1, _, _, _, hcG, _, _⟩ :=
    HAE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let Z := fun r => partialCoreDownwardReturnState (Y r)
  let u := fun r => Z r 1
  let w := fun r => Z r 2
  have hrepr (r : ℝ) : ![f r, u r, w r] = Z r := by
    ext i
    fin_cases i <;> rfl
  have hf : DifferentiableAt ℝ f ρ := differentiableAt_pi.mp HZ 0
  have hu : DifferentiableAt ℝ u ρ := differentiableAt_pi.mp HZ 1
  have hw : DifferentiableAt ℝ w ρ := differentiableAt_pi.mp HZ 2
  have Hwall (i : Fin 2) : |deriv (fun r => Z r i.succ) ρ| ≤ Real.sqrt (Z ρ i.succ) * |deriv f ρ| := by
    apply (Hcone i).trans
    have hb : 1 - 1 / (16 * restartShearTailEntranceRadius h a q D ζ ν ρ) ≤ 1 := by
      have hk0 : 0 < restartShearTailEntranceRadius h a q D ζ ν ρ := by linarith only [hκ]
      have H : 0 ≤ 1 / (16 * restartShearTailEntranceRadius h a q D ζ ν ρ) := by positivity
      linarith only [H]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)) (abs_nonneg (deriv f ρ))
  have hpρ : coreExitConnectionParameters ![f ρ, u ρ, w ρ] = p ρ := by rw [hrepr]; rfl
  have Hconn := connectionReturn_coreExit_curve hf hu hw hf1 hdf ⟨hη0, hη⟩ hsη hηL
    (by rw [hpρ]; exact hμ.1) (by rw [hpρ]; exact hU) hW (Hwall 0) (Hwall 1)
  have heq : (fun r => connectionReturnPhysicalState (coreExitConnectionParameters ![f r, u r, w r])) = G := by
    funext r
    rw [hrepr]
    rfl
  change DifferentiableAt ℝ (fun r => connectionReturnPhysicalState (coreExitConnectionParameters ![f r, u r, w r])) ρ ∧ _ at Hconn
  rw [heq] at Hconn
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := Hconn
  change |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * coreExitConnectionParameters ![f ρ, u ρ, w ρ] 0) at hratio
  rw [hpρ] at hratio
  have hg : DifferentiableAt ℝ g ρ := differentiableAt_pi.mp hG 0
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ((ζ, ν), r)) ρ := by fun_prop
  refine ⟨hcG.comp ρ hc, hf, hf1, hg0, hdf, hdg, hratio, hratioBounds, ?_, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩
  intro i
  fin_cases i
  · exact hgu
  · exact hgw

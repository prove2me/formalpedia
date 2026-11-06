-- Prove2me | solution 1 for BianchiIX.exists_restartShearReturn_common_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:07:00.079792+00:00
-- url     : https://prove2.me/submissions/fbe9a04e-8891-4b1d-a3c6-f841ff6926d2

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
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
import Theorems.Thm_BianchiIX_exists_restartShearEntrance_connection
import Theorems.Thm_BianchiIX_exists_restartShearEntrance_core_cone
import Theorems.Thm_BianchiIX_exists_restartShearReturn_cone
import Theorems.Thm_BianchiIX_exists_restartShearTail_connection_curve
import Theorems.Thm_BianchiIX_exists_restartShearTail_cutoff_germs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearEntrance_connection_curve :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let p := restartShearReturnParameters h s n₂ n₃
            let G := restartShearReturnState h s n₂ n₃
            let g := fun r => G r 0
            Y ρ 2 < 1 → ContDiffAt ℝ 2 G ρ ∧ DifferentiableAt ℝ f ρ ∧
              1 < f ρ ∧ 0 < g ρ ∧ deriv f ρ < 0 ∧ deriv g ρ < 0 ∧
              |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
              (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
              (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
              DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧
              DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
              (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
              2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
              deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
                (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearEntrance_core_cone
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_connection
  obtain ⟨η, hη0, hη, hsη, hηL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP η ⟨hη0, hη⟩
  refine ⟨min aC aE, lt_min haC haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y f p G g hv
  obtain ⟨hκ, _, HZ, _, hdf, _, _, Hcone⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, hμ, hU, hW, _, _, hf1, _, _, _, hcG, _, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
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
    have hb : 1 - 1 / (16 * coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2)) ≤ 1 := by
      have H : 0 ≤ 1 / (16 * coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2)) := by
        have hk0 : 0 < coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2) := by
          linarith only [hκ]
        positivity
      linarith only [H]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)) (abs_nonneg (deriv f ρ))
  have hpρ : coreExitConnectionParameters ![f ρ, u ρ, w ρ] = p ρ := by rw [hrepr]; rfl
  have Hconn := connectionReturn_coreExit_curve hf hu hw hf1 hdf ⟨hη0, hη⟩ hsη hηL
    (by rw [hpρ]; exact hμ.1)
    (by rw [hpρ]; exact hU) hW (Hwall 0) (Hwall 1)
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
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ((n₂, n₃), r)) ρ := by fun_prop
  refine ⟨hcG.comp ρ hc, hf, hf1, hg0, hdf, hdg, hratio, hratioBounds, ?_, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩
  intro i
  fin_cases i
  · exact hgu
  · exact hgw

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_all_active_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let G := restartShearReturnState h s n₂ n₃
            let g := fun r => G r 0
            ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
              (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
              ContDiffAt ℝ 2 (restartShearReturnPhase h s n₂ n₃) ρ ∧
              0 < deriv (restartShearReturnPhase h s n₂ n₃) ρ := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearReturn_cone
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_connection_curve
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s G g
  have H : ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
      ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
    by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
    · obtain ⟨hc, hneg, hU, hW⟩ :=
        HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
      refine ⟨hc, hneg, ?_⟩
      intro i
      fin_cases i
      · exact hU
      · exact hW
    · obtain ⟨hc, _, _, _, _, hneg, _, _, hcone, _⟩ :=
        HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
      exact ⟨hc, hneg, hcone⟩
  have hg0 : g ρ ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartShearReturnParameters h s n₂ n₃ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hg : ContDiffAt ℝ 2 g ρ := contDiffAt_pi.mp H.1 0
  exact ⟨H.1, H.2.1, H.2.2, contDiffAt_const.div hg hg0,
    reciprocal_curve_derivative_pos (hg.differentiableAt (by norm_num)) hg0 H.2.1⟩

end
end

private theorem BianchiIX.exists_restartShearTail_fast_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s ζ ν
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection_curve
  refine ⟨min hG hC, lt_min hhG hhC, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aG aC, lt_min haG haC, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s G g
  have H := (HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ).2.1
  have hi : ContinuousAt (fun r : ℝ => ((ζ, ν), r)) ρ := continuousAt_const.prodMk continuousAt_id
  have Heq : G =ᶠ[𝓝 ρ] restartShearReturnState h (shearTailTime a D + s) ζ ν := hi.tendsto.eventually H
  have Heqi (i : Fin 3) : (fun r => G r i) =ᶠ[𝓝 ρ]
      (fun r => restartShearReturnState h (shearTailTime a D + s) ζ ν r i) :=
    Heq.mono fun _ hv => congrFun hv i
  obtain ⟨hc, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hc.congr_of_eventuallyEq Heq, ?_, ?_⟩
  · change deriv (fun r => G r 0) ρ < 0
    rw [(Heqi 0).deriv_eq]
    exact hneg
  · intro i
    change |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv (fun r => G r 0) ρ|
    rw [(Heqi i.succ).deriv_eq, (Heqi 0).deriv_eq, Heq.self_of_nhds]
    exact hcone i

/-- The single positive-shear return preserves the square-root cone for either choice of the small wall. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s n₂ n₃
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_cone
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_cone
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s G g
  by_cases hn₃ : n₃ ≤ a ^ P
  · obtain ⟨hc, hneg, hcone, _⟩ := HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
    exact ⟨hc, hneg, hcone⟩
  · exact HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ

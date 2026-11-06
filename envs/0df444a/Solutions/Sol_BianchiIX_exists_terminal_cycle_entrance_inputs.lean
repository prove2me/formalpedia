-- Prove2me | solution 1 for BianchiIX.exists_terminal_cycle_entrance_inputs
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:10:59.578544+00:00
-- url     : https://prove2.me/submissions/6615c3ae-d06f-49c2-a85a-4a2a8df800ec

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_weighted_power {α k a c e : ℝ} {p q : ℕ}
    (hα : 0 < α) (hk : 0 ≤ k) (hkc : k ≤ c / α) (he : 0 ≤ e)
    (ha : a ≤ e * α ^ p) (hp : q ≤ p) :
    a * k ^ q ≤ e * c ^ q * α ^ (p - q) := by
  calc
    a * k ^ q ≤ (e * α ^ p) * (c / α) ^ q :=
      (mul_le_mul_of_nonneg_right ha (pow_nonneg hk q)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk hkc q) (mul_nonneg he (pow_nonneg hα.le p)))
    _ = e * c ^ q * α ^ (p - q) := by
      have hpα : α ^ p = α ^ (p - q) * α ^ q := by rw [← pow_add, Nat.sub_add_cancel hp]
      rw [hpα, div_pow]
      field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_scaled_wall_power {α B δ : ℝ} {p : ℕ}
    (hα : 0 < α) (hp : 2 ≤ p) (hB : B ≤ δ * α ^ p) :
    2 * B / α ^ 2 ≤ 2 * δ * α ^ (p - 2) := by
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hpα : α ^ p = α ^ (p - 2) * α ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hp]
  rw [hpα] at hB
  nlinarith only [hB]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_entrance_power {α k a e ε : ℝ} {p q : ℕ}
    (hα : 0 < α ∧ α ≤ 1) (hk : 0 ≤ k) (hkc : k ≤ (11 / 5) / α)
    (he : 0 ≤ e) (heε : e ≤ ε / (4 * (11 / 5) ^ q))
    (ha : a ≤ 2 * e * α ^ (p - 2)) (hp : q + 2 ≤ p) :
    a * k ^ q ≤ 2 * e * (11 / 5) ^ q * α ^ (p - q - 2) ∧ a * k ^ q ≤ ε / 2 := by
  have H := exitCycle_weighted_power hα.1 hk hkc (mul_nonneg (by norm_num) he) ha (by omega : q ≤ p - 2)
  have hexp : p - 2 - q = p - q - 2 := by omega
  rw [hexp] at H
  refine ⟨H, H.trans ?_⟩
  have hpow : α ^ (p - q - 2) ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have hcoeff := (le_div_iff₀ (by positivity : 0 < 4 * (11 / 5 : ℝ) ^ q)).mp heε
  have H1 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * e * (11 / 5 : ℝ) ^ q)
  nlinarith only [H1, hcoeff]

end
end


/-- One choice of constants puts every cyclic endpoint in the prescribed power-small entrance domain. -/
theorem solution {εin η : ℝ} (hεin : 0 < εin)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let k := coreRadius (z 0) (z 2)
      let γ := normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0
      coreTailValid h Y ∧ toProjectiveState (γ (coreTailTime h Y)) = z ∧
        7 / 4 < k ∧ 2 < z 0 ∧
        (0 < z 1 ∧ z 1 ≤ εin ∧ z 1 * k ^ q ≤ εin / 2) ∧
        (0 < z 2 ∧ z 2 < 1 / 2) ∧
        (0 < z 3 ∧ z 3 ≤ εin ∧ z 3 * k ^ q ≤ εin / 2) ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y), 0 < 1 + γ t 0 ∧ |toProjectiveState (γ t) 2| ≤ 1 / 5000) ∧
        0 < projectiveCycleDenom (coreTailState h Y) := by
  obtain ⟨C, hC, ε₀, hε₀, HE⟩ := exists_terminal_axisCycle_endpoint hη (by omega : 2 ≤ J)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let δ := εin / (4 * (11 / 5 : ℝ) ^ q)
  have hδ : 0 < δ := div_pos hεin (by positivity)
  let ε := min ε₀ (δ / C)
  have hε : 0 < ε := lt_min hε₀ (div_pos hδ hC0)
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h z k γ
  have hα0 : 0 < α := hα.1
  have hsmall₀ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ (δ / C)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, HEq, HH, HM, HK, HU, HW, HP, HF⟩ := HE α b u w hα hb hsmall₀ hsum
  have hbudget : C * b ≤ δ * α ^ (2 * J) := by
    have Hε := (le_div_iff₀ hC0).mp (min_le_right ε₀ (δ / C))
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hk : 7 / 4 < k := by dsimp only [k, z]; linarith only [HK.1, hlow]
  have hm : 2 < z 0 := by dsimp only [z]; linarith only [HM.1, hlow]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hkc : k ≤ (11 / 5) / α := HK.2.le.trans_eq (by ring)
  have hU : 0 < z 1 := lt_of_lt_of_le (mul_pos (div_pos hη.1 (by norm_num)) (pow_pos hα.1 (J - 2))) HU.1
  have hpos : 0 < z 2 ∧ 0 < z 3 := HP ⟨hu, hw⟩
  have hPu := (exitCycle_entrance_power hα hk0 hkc hη.1.le hηin HU.2 hJ).2
  have hWpower : z 3 ≤ 2 * δ * α ^ (2 * J - 2) :=
    (le_abs_self _).trans (HW.2.trans (exitCycle_scaled_wall_power hα.1 (by omega) hbudget))
  have hPw := (exitCycle_entrance_power hα hk0 hkc hδ.le le_rfl hWpower (by omega : q + 2 ≤ 2 * J)).2
  have hkp : 1 ≤ k ^ q := one_le_pow₀ (by linarith only [hk] : 1 ≤ k)
  have hsmallwall {a : ℝ} (ha : 0 < a) (hP : a * k ^ q ≤ εin / 2) : a ≤ εin := by
    nlinarith only [mul_le_mul_of_nonneg_left hkp ha.le, hP, hεin]
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨HV.1.1.1.le, le_rfl⟩
  have hvbound := (HF _ ht).2
  rw [HEq] at hvbound
  exact ⟨HV, HEq, hk, hm, ⟨hU, hsmallwall hU hPu, hPu⟩,
    ⟨hpos.1, by linarith only [le_abs_self (z 2), hvbound]⟩,
    ⟨hpos.2, hsmallwall hpos.2 hPw, hPw⟩, HF, lt_trans (by positivity) HH.1⟩

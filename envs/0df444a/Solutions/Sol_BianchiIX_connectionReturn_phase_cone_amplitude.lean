-- Prove2me | solution 1 for BianchiIX.connectionReturn_phase_cone_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:31:16.401366+00:00
-- url     : https://prove2.me/submissions/b9a9e552-896c-48a0-8c25-aa13412e2dbd

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Theorems.Thm_BianchiIX_connectionReturn_phase_response_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.three_coordinate_expansion (v : Fin 3 → ℝ) :
    v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.three_coordinate_linear_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    |A v| ≤ |v 0| * |A ![1, 0, 0]| + |v 1| * |A ![0, 1, 0]| + |v 2| * |A ![0, 0, 1]| := by
  have hid : A v = v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0] + v 2 * A ![0, 0, 1] := by
    conv_lhs => rw [three_coordinate_expansion v]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hid]
  simpa only [abs_mul] using
    (abs_add_le (v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0]) (v 2 * A ![0, 0, 1])).trans
      (add_le_add (abs_add_le (v 0 * A ![1, 0, 0]) (v 1 * A ![0, 1, 0])) le_rfl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_connectionReturnPhaseError {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhaseError p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  have hcoord : ContDiffAt ℝ 2 (fun q => connectionReturnState q 0) p := contDiffAt_pi.mp hstate 0
  have hleft : ContDiffAt ℝ 2 (fun q => phaseNorm (-connectionReturnState q 0 - 1) 1) p := by
    apply (((hcoord.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt
    positivity
  have hright : ContDiffAt ℝ 2 (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1) p := by
    have hq : ContDiffAt ℝ 2 (fun q : ConnectionParameters => q 0 + 1) p := by fun_prop
    apply ((hq.pow 2).add contDiffAt_const).sqrt
    positivity
  exact (hleft.sub hright).add contDiffAt_const

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_phase_response_bounds_nonneg {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  by_cases hpos : 0 < p 1
  · exact connectionReturn_phase_response_bounds hμ ⟨hpos, hu.2⟩ hw
  have hp1 : p 1 = 0 := le_antisymm (le_of_not_gt hpos) hu.1
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  let ε : ℝ := (1 / 10000) / p 0
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q : ℕ → ConnectionParameters := fun n => ![p 0, ε / ((n : ℝ) + 1), p 2]
  have hqU (n : ℕ) : 0 < q n 1 ∧ q n 1 ≤ (1 / 10000) / q n 0 := by
    change 0 < ε / ((n : ℝ) + 1) ∧ ε / ((n : ℝ) + 1) ≤ ε
    exact ⟨div_pos hε (by positivity), div_le_self hε.le (by have H : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith only [H])⟩
  have hq : Tendsto q atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
      simpa [q, hp1, div_eq_mul_inv] using H
    · exact tendsto_const_nhds
  have H (n : ℕ) := connectionReturn_phase_response_bounds (p := q n) hμ (hqU n) hw
  have hd (v : ConnectionParameters) : ContinuousAt (fun r => |fderiv ℝ connectionReturnPhaseError r v|) p :=
    (((contDiffAt_connectionReturnPhaseError hμ hu hw).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).abs
  have hRμ : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + (r 2) ^ 2) / (r 0) ^ 2) p := by
    fun_prop (disch := exact pow_ne_zero 2 hμne)
  have hRU : ContinuousAt (fun r : ConnectionParameters => 50000 / r 0) p := by
    exact continuousAt_const.div (continuous_apply (0 : Fin 3)).continuousAt hμne
  have hRW : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + r 2) / r 0) p := by
    fun_prop (disch := exact hμne)
  exact ⟨le_of_tendsto_of_tendsto' ((hd ![1, 0, 0]).tendsto.comp hq) (hRμ.tendsto.comp hq) (fun n => (H n).1),
    le_of_tendsto_of_tendsto' ((hd ![0, 1, 0]).tendsto.comp hq) (hRU.tendsto.comp hq) (fun n => (H n).2.1),
    le_of_tendsto_of_tendsto' ((hd ![0, 0, 1]).tendsto.comp hq) (hRW.tendsto.comp hq) (fun n => (H n).2.2)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_unit_phase_direction {p v : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1) : |v 0| ≤ 2 := by
  have H := phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p 0 + 1) (by norm_num)
  have hR : 0 < (p 0 + 1) / phaseNorm (p 0 + 1) 1 := by linarith only [H.1]
  have hv0 : 0 ≤ v 0 := by nlinarith only [hv, hR]
  rw [abs_of_nonneg hv0]
  have HH := mul_le_mul_of_nonneg_right H.1 hv0
  nlinarith only [HH, hv]

end
end


/-- The phase response retains the actual incoming amplitude rather than only its uniform threshold. -/
theorem solution {p v : ConnectionParameters}
    (hμ : 4 ≤ p 0) (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0)
    (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    |fderiv ℝ connectionReturnPhaseError p v| ≤ 150000 * Real.sqrt (p 1 + p 2) / p 0 := by
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu1 : p 1 ≤ 1 / 10000 := hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))
  have hb : 0 ≤ p 1 + p 2 := add_nonneg hu.1.le hw.1.le
  have hb1 : p 1 + p 2 ≤ 1 := by linarith only [hu1, hw.2]
  have hw1 : p 2 ≤ 1 := by linarith only [hw.2]
  have hbs : p 1 + p 2 ≤ Real.sqrt (p 1 + p 2) := by
    have hs := Real.sqrt_le_one.mpr hb1
    nlinarith only [Real.sq_sqrt hb, Real.sqrt_nonneg (p 1 + p 2),
      mul_nonneg (Real.sqrt_nonneg (p 1 + p 2)) (sub_nonneg.mpr hs)]
  have hw2 : p 2 ^ 2 ≤ p 2 := by nlinarith only [hw.1.le, hw1]
  have hfirst : 2 * (p 1 + p 2 ^ 2) / p 0 ≤ Real.sqrt (p 1 + p 2) := by
    apply (div_le_iff₀ hμ0).mpr
    have H := mul_le_mul_of_nonneg_right hμ (Real.sqrt_nonneg (p 1 + p 2))
    nlinarith only [H, hw2, hbs, Real.sqrt_nonneg (p 1 + p 2)]
  have hsu : Real.sqrt (p 1) ≤ Real.sqrt (p 1 + p 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1.le)
  have hsw : Real.sqrt (p 2) ≤ Real.sqrt (p 1 + p 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1.le)
  have hlast : (p 1 + p 2) * Real.sqrt (p 2) ≤ Real.sqrt (p 1 + p 2) :=
    (mul_le_mul_of_nonneg_right hb1 (Real.sqrt_nonneg _)).trans (by simpa using hsw)
  have hsize : 2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
      (p 1 + p 2) * Real.sqrt (p 2) ≤ 3 * Real.sqrt (p 1 + p 2) := by
    linarith only [hfirst, hsu, hlast]
  have H := connectionReturn_phase_response_bounds_nonneg hμ ⟨hu.1.le, hu.2⟩ hw
  have H0 := mul_le_mul (connection_unit_phase_direction hμ hv) H.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H1 := mul_le_mul hvu H.2.1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have H2 := mul_le_mul hvw H.2.2 (abs_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ 2 * (50000 * (p 1 + p 2 ^ 2) / p 0 ^ 2) +
        Real.sqrt (p 1) * (50000 / p 0) + Real.sqrt (p 2) * (50000 * (p 1 + p 2) / p 0) :=
      (three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError p) v).trans
        (add_le_add (add_le_add H0 H1) H2)
    _ = (50000 / p 0) * (2 * (p 1 + p 2 ^ 2) / p 0 + Real.sqrt (p 1) +
        (p 1 + p 2) * Real.sqrt (p 2)) := by ring
    _ ≤ (50000 / p 0) * (3 * Real.sqrt (p 1 + p 2)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by ring

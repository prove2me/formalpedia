-- Prove2me | solution 1 for BianchiIX.connectionLog_actual_radial_variation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T10:08:47.950078+00:00
-- url     : https://prove2.me/submissions/b1331a87-4afc-459e-b686-827a238d71ab

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseKernel
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWallDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseNumerator
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionFlowVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionCoefficientMatrix
import Definitions.Def_BianchiIX_Analysis_ConnectionLogCoordinates
import Definitions.Def_BianchiIX_Analysis_ConnectionLogLinearization
import Definitions.Def_BianchiIX_Analysis_ConnectionWeightedVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionFeedbackBounds
import Definitions.Def_BianchiIX_Dynamics_ConnectionLogFlowVariation
import Theorems.Thm_BianchiIX_connectionLogField_components
import Theorems.Thm_BianchiIX_connectionLog_radial_variation_bounds
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_clock_variation
import Theorems.Thm_BianchiIX_hasDerivAt_observable_variation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_clock_identities {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w =
      -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w ∧
    connectionStrongRate m u v w / connectionSpeed m u v w + (m + 1) / 2 =
      (-(v - w) ^ 2 + u ^ 2 - (m + 1) * coupling u v w) / (2 * connectionSpeed m u v w) := by
  constructor <;> dsimp [connectionSpeed, connectionStrongRate] at * <;> field_simp <;> ring

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

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_interaction {m v w : ℝ} (hm : 1 < m) :
    v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
      w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) = (v * w) ^ 2 * matchingPhaseKernel m v w := by
  have hp := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_ratio_defect (b := w) (show 0 < m - 1 by linarith only [hm])
  have hn' : (m - 1) / phaseNorm (m - 1) w - 1 = -(w ^ 2 * phaseNormKernel (m - 1) w) := by
    linarith only [hn]
  rw [hp, hn']
  unfold matchingPhaseKernel
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_directional {m u v w : ℝ} (hm : 1 < m) :
    matchingPhaseSlope m v w * (-phaseVelocity (-m) u v w) +
      v / phaseNorm (m + 1) v * activeVelocity (-m) u v w +
      w / phaseNorm (m - 1) w * weakVelocity (-m) u v w = matchingPhaseRate m u v w := by
  calc
    _ = v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
        w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) -
        u * matchingPhaseSlope m v w * (v - w) - coupling u v w * matchingPhaseWeight m v w := by
      dsimp [matchingPhaseSlope, matchingPhaseWeight, phaseVelocity, activeVelocity, weakVelocity]
      ring
    _ = _ := by rw [matchingPhase_interaction hm]; rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s))
      (matchingPhaseSlope (m t) (v t) (w t) * m' +
        v t / phaseNorm (m t + 1) (v t) * v' + w t / phaseNorm (m t - 1) (w t) * w') t := by
  have hp : (m t + 1) ^ 2 + v t ^ 2 ≠ 0 := by
    have H : 0 < m t + 1 := by linarith only [hmt]
    positivity
  have hn : (m t - 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have H : 0 < m t - 1 := by linarith only [hmt]
    positivity
  have H := ((((hm.add_const 1).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub_const 1).pow 2).add (hw.pow 2)).sqrt hn)
  convert! H.sub hm using 1
  dsimp [matchingPhaseSlope, phaseNorm]
  ring

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

private theorem BianchiIX.matchingPhase_slope_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 / 4 ≤ matchingPhaseSlope m v w ∧ matchingPhaseSlope m v w ≤ 1 := by
  have hp := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m + 1) hv
  have hn := phaseNorm_ratio_bounds (by linarith only [hμ, (abs_le.mp hm).1] : 2 ≤ m - 1) hw
  dsimp [matchingPhaseSlope]
  constructor <;> linarith only [hp.1, hp.2, hn.1, hn.2]

end
end

section
noncomputable section
open BianchiIX
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.contDiffAt_matchingPhase_comp {m v w : E → ℝ} {p : E} (n : WithTop ℕ∞)
    (hm : ContDiffAt ℝ n m p) (hv : ContDiffAt ℝ n v p) (hw : ContDiffAt ℝ n w p)
    (hmt : 1 < m p) : ContDiffAt ℝ n (fun q => matchingPhase (m q) (v q) (w q)) p := by
  have hp : (m p + 1) ^ 2 + v p ^ 2 ≠ 0 := by
    have H : 0 < m p + 1 := by linarith only [hmt]
    positivity
  have hn : (m p - 1) ^ 2 + w p ^ 2 ≠ 0 := by
    have H : 0 < m p - 1 := by linarith only [hmt]
    positivity
  exact (((((hm.add contDiffAt_const).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub contDiffAt_const).pow 2).add (hw.pow 2)).sqrt hn)).sub hm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_coupling {u v w : ℝ → ℝ} {u' v' w' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => coupling (u s) (v s) (w s))
      (u' * (v t + w t - 2 * u t) + u t * (v' + w')) t := by
  convert! hu.mul ((hv.add hw).sub hu) using 1
  dsimp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionSpeed {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => connectionSpeed (m s) (u s) (v s) (w s))
      (m' - (u' * (v t + w t - 2 * u t) + u t * (v' + w'))) t :=
  (hm.sub_const 1).sub (hasDerivAt_coupling hu hv hw)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionStrongClockRate {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionStrongClockRate (m s) (u s) (v s) (w s))
      ((-m t * m' - (v t - w t) * (v' - w') + u t * u' -
        connectionStrongClockRate (m t) (u t) (v t) (w t) *
          (m' - (u' * (v t + w t - 2 * u t) + u t * (v' + w')))) /
        connectionSpeed (m t) (u t) (v t) (w t)) t := by
  have hN : HasDerivAt (fun s => connectionStrongRate (m s) (u s) (v s) (w s))
      (-m t * m' - (v t - w t) * (v' - w') + u t * u') t := by
    convert! ((((hm.pow 2).const_sub 1).sub ((hv.sub hw).pow 2)).add (hu.pow 2)).div_const 2 using 1
    dsimp
    ring
  apply (hN.div (hasDerivAt_connectionSpeed hm hu hv hw) hD).congr_deriv
  dsimp [connectionStrongClockRate]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionWeakClockRate {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionWeakClockRate (m s) (u s) (v s) (w s))
      ((2 * (1 + coupling (u t) (v t) (w t)) * m' -
        2 * m t * (u' * (v t + w t - 2 * u t) + u t * (v' + w'))) /
        connectionSpeed (m t) (u t) (v t) (w t) ^ 2) t := by
  have H := ((((hasDerivAt_coupling hu hv hw).const_add 1).const_mul 2).div
    (hasDerivAt_connectionSpeed hm hu hv hw) hD).const_sub (-1)
  apply H.congr_deriv
  dsimp [connectionSpeed]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connection_clock_weighted_curves {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionStrongClockRate (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionStrongClockPartials (m t) (u t) (v t) (w t) i * d i) t ∧
    HasDerivAt (fun s => connectionWeakClockRate (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionWeakClockPartials (m t) (u t) (v t) (w t) i * d i) t := by
  constructor
  · apply (hasDerivAt_connectionStrongClockRate hm hu hv hw hD).congr_deriv
    simp [Fin.sum_univ_succ, connectionStrongClockPartials]
    ring
  · apply (hasDerivAt_connectionWeakClockRate hm hu hv hw hD).congr_deriv
    simp [Fin.sum_univ_succ, connectionWeakClockPartials]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_phaseNorm {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => phaseNorm (a s) (b s))
      ((a t * a' + b t * b') / phaseNorm (a t) (b t)) t := by
  have hpos : a t ^ 2 + b t ^ 2 ≠ 0 := by positivity
  convert! ((ha.pow 2).add (hb.pow 2)).sqrt hpos using 1
  dsimp [phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_phaseNormKernel {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => phaseNormKernel (a s) (b s))
      (phaseNormKernelDa (a t) (b t) * a' + phaseNormKernelDb (a t) (b t) * b') t := by
  have hK := phaseNorm_pos (b := b t) ha0
  have hS : 0 < phaseNorm (a t) (b t) + a t := add_pos hK ha0
  have hN := hasDerivAt_phaseNorm ha hb ha0
  have H := (hN.mul (hN.add ha)).inv (ne_of_gt (mul_pos hK hS))
  simp only [phaseNormKernel, one_div]
  apply H.congr_deriv
  dsimp [phaseNormKernelDa, phaseNormKernelDb]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhaseKernel {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseKernel (m s) (v s) (w s))
      (matchingPhaseKernelDm (m t) (v t) (w t) * m' +
        phaseNormKernelDb (m t + 1) (v t) * v' - phaseNormKernelDb (m t - 1) (w t) * w') t := by
  apply ((hasDerivAt_phaseNormKernel (hm.add_const 1) hv (by linarith only [hmt])).sub
    (hasDerivAt_phaseNormKernel (hm.sub_const 1) hw (by linarith only [hmt]))).congr_deriv
  dsimp [matchingPhaseKernelDm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhaseKernel_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseKernel (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseKernelPartials (m t) (v t) (w t) i * d i) t := by
  apply (hasDerivAt_matchingPhaseKernel hm hv hw hmt).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseKernelPartials]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionPhaseG_decomposition (m u v w : ℝ) :
    connectionPhaseG m u v w = u * connectionPhaseA m u v w + (v * w) ^ 2 * connectionPhaseB m u v w := by
  dsimp [connectionPhaseG, connectionPhaseA, connectionPhaseB, matchingPhaseRate, coupling]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionSpeed_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) :
    HasDerivAt (fun s => connectionSpeed (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) t := by
  apply (hasDerivAt_connectionSpeed hm hu hv hw).congr_deriv
  simp [Fin.sum_univ_succ, connectionSpeedPartials]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionPhaseB_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseB (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseBPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hR := hasDerivAt_matchingPhaseKernel_weighted d hm hv hw hmt
  have hd := hasDerivAt_connectionSpeed_weighted d hm hu hv hw
  have H : HasDerivAt (fun s => connectionPhaseB (m s) (u s) (v s) (w s))
      ((∑ i : Fin 4, matchingPhaseKernelPartials (m t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t) -
        matchingPhaseKernel (m t) (v t) (w t) *
          (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t) ^ 2) t := by
    apply (hR.div hd hD).congr_deriv
    field_simp
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseBPartials]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhaseWeight_identity {m v w : ℝ} (hm : 1 < m) :
    matchingPhaseWeight m v w = matchingPhase m v w - (m + 1) / phaseNorm (m + 1) v +
      (m - 1) / phaseNorm (m - 1) w := by
  have hp := phaseNorm_pos (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_pos (b := w) (show 0 < m - 1 by linarith only [hm])
  dsimp [matchingPhaseWeight, matchingPhaseSlope, matchingPhase]
  field_simp
  linear_combination -phaseNorm (m - 1) w * phaseNorm_sq (m + 1) v -
    phaseNorm (m + 1) v * phaseNorm_sq (m - 1) w

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_phaseNormRatio {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => a s / phaseNorm (a s) (b s))
      ((b t ^ 2 * a' - a t * b t * b') / phaseNorm (a t) (b t) ^ 3) t := by
  have hK := phaseNorm_pos (b := b t) ha0
  apply (ha.div (hasDerivAt_phaseNorm ha hb ha0) (ne_of_gt hK)).congr_deriv
  field_simp
  linear_combination a' * phaseNorm_sq (a t) (b t)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_matchingPhase_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s)) (d 0) t := by
  apply (hasDerivAt_matchingPhase hm hv hw hmt).congr_deriv
  dsimp [matchingPhaseVVariation, matchingPhaseWVariation]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_matchingPhaseSlope_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseSlope (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseSlopePartials (m t) (v t) (w t) i * d i) t := by
  have hp := hasDerivAt_phaseNormRatio (hm.add_const 1) hv (by linarith only [hmt])
  have hn := hasDerivAt_phaseNormRatio (hm.sub_const 1) hw (by linarith only [hmt])
  apply ((hp.add hn).sub_const 1).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseSlopePartials, matchingPhaseSlopeDm]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_matchingPhaseWeight_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => matchingPhaseWeight (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseWeightPartials (m t) (v t) (w t) i * d i) t := by
  have hp := hasDerivAt_phaseNormRatio (hm.add_const 1) hv (by linarith only [hmt])
  have hn := hasDerivAt_phaseNormRatio (hm.sub_const 1) hw (by linarith only [hmt])
  have hF := hasDerivAt_matchingPhase_weighted d hm hv hw hmt hf
  have H := (hF.sub hp).add hn
  have heq : (fun s => matchingPhaseWeight (m s) (v s) (w s)) =ᶠ[𝓝 t]
      ((fun s => matchingPhase (m s) (v s) (w s)) - (fun s => (m s + 1) / phaseNorm (m s + 1) (v s)) +
        (fun s => (m s - 1) / phaseNorm (m s - 1) (w s))) := by
    filter_upwards [hm.continuousAt.eventually (eventually_gt_nhds hmt)] with s hs
    exact matchingPhaseWeight_identity hs
  apply (H.congr_of_eventuallyEq heq).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseWeightPartials, matchingPhaseWeightDm]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionPhaseNumerator_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseNumerator (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseNumeratorPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hF := hasDerivAt_matchingPhaseSlope_weighted d hm hv hw hmt
  have hH := hasDerivAt_matchingPhaseWeight_weighted d hm hv hw hmt hf
  apply ((hF.mul (hv.sub hw)).add (((hv.add hw).sub hu).mul hH)).congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseNumeratorPartials, matchingPhaseSlopePartials,
    matchingPhaseWeightPartials, Pi.sub_apply, Pi.add_apply]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionPhaseA_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseA (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseAPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hN := hasDerivAt_connectionPhaseNumerator_weighted d hm hu hv hw hmt hf
  have hd := hasDerivAt_connectionSpeed_weighted d hm hu hv hw
  have H : HasDerivAt (fun s => connectionPhaseA (m s) (u s) (v s) (w s))
      (-(∑ i : Fin 4, connectionPhaseNumeratorPartials (m t) (u t) (v t) (w t) i * d i) /
        connectionSpeed (m t) (u t) (v t) (w t) -
        connectionPhaseA (m t) (u t) (v t) (w t) *
          (∑ i : Fin 4, connectionSpeedPartials (m t) (u t) (v t) (w t) i * d i) /
          connectionSpeed (m t) (u t) (v t) (w t)) t := by
    apply (hN.neg.div hd hD).congr_deriv
    dsimp [connectionPhaseA, connectionPhaseNumerator]
    field_simp
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseAPartials]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionPhaseG_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionPhaseG (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionPhaseGPartials (m t) (u t) (v t) (w t) i * d i) t := by
  have hA := hasDerivAt_connectionPhaseA_weighted d hm hu hv hw hmt hf hD
  have hB := hasDerivAt_connectionPhaseB_weighted d hm hu hv hw hmt hD
  have H := (hu.mul hA).add (((hv.mul hw).pow 2).mul hB)
  have heq : (fun s => connectionPhaseG (m s) (u s) (v s) (w s)) =
      (fun s => u s * connectionPhaseA (m s) (u s) (v s) (w s) +
        (v s * w s) ^ 2 * connectionPhaseB (m s) (u s) (v s) (w s)) := by
    funext s
    exact connectionPhaseG_decomposition _ _ _ _
  rw [heq]
  apply H.congr_deriv
  simp [Fin.sum_univ_succ, connectionPhaseGPartials, Pi.mul_apply]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_connectionLogField (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : connectionClockRate y ≠ 0) : ContDiffAt ℝ n connectionLogField y := by
  exact ((contDiff_connectionClockRate n).contDiffAt.inv hD).smul
    (contDiff_projectiveField n).contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_connectionLogClock (n : WithTop ℕ∞) {y : ProjectiveState}
    (hw : y 3 ≠ 0) : ContDiffAt ℝ n connectionLogClock y :=
  (contDiff_apply ℝ ℝ 3).contDiffAt.log hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_connectionOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n connectionOriginalClockRate y := by
  unfold connectionOriginalClockRate
  exact (contDiffAt_const.div (contDiff_projectiveStateDenom n).contDiffAt hD).mul
    (contDiff_connectionClockRate n).contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogClock_fderiv {y : ProjectiveState} (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogClock y v = v 3 / y 3 := by
  have H := ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw)
  rw [show fderiv ℝ connectionLogClock y = _ from H.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogClock_fderiv_field {y : ProjectiveState} (hw : y 3 ≠ 0) :
    fderiv ℝ connectionLogClock y (projectiveOriginalField y) = connectionOriginalClockRate y := by
  rw [connectionLogClock_fderiv hw]
  change (6 / projectiveStateDenom y * weakVelocity (y 0) (y 1) (y 2) (y 3)) / y 3 = _
  dsimp [connectionOriginalClockRate, connectionClockRate, connectionSpeed, weakVelocity]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveOriginalField_connectionLog {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    projectiveOriginalField y = connectionOriginalClockRate y • connectionLogField y := by
  unfold connectionOriginalClockRate connectionLogField projectiveOriginalField
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogField_amplitude {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    connectionLogField y 1 = connectionStrongClockRate (-y 0) (y 1) (y 2) (y 3) * y 1 ∧
    connectionLogField y 2 = connectionWeakClockRate (-y 0) (y 1) (y 2) (y 3) * y 2 := by
  have H := connectionLogField_components hD
  have hb := (connection_clock_identities hD).1
  simp only [neg_neg] at hb
  refine ⟨H.2.1, ?_⟩
  rw [H.2.2.1]
  dsimp only [connectionClockRate, connectionWeakClockRate]
  rw [hb]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLog_amplitudes {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hD : connectionClockRate (Y t) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 1)) (connectionStrongClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t ∧
    HasDerivAt (fun s => Real.log (Y s 2)) (connectionWeakClockRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := connectionLogField_amplitude hD
  constructor
  · apply ((hasDerivAt_pi.mp hY 1).log hu).congr_deriv
    rw [H.1, mul_div_cancel_right₀ _ hu]
  · apply ((hasDerivAt_pi.mp hY 2).log hv).congr_deriv
    rw [H.2, mul_div_cancel_right₀ _ hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (a * matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have H := hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
    (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  simp only [Pi.neg_apply] at H
  have hrate := matchingPhase_directional (u := Y t 1) (v := Y t 2) (w := Y t 3) hm
  simp only [neg_neg] at hrate
  convert! H using 1
  rw [← hrate]
  change a * _ = matchingPhaseSlope _ _ _ * (-(a * phaseVelocity _ _ _ _)) +
    _ * (a * activeVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_matchingPhase_connectionLog {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0) :
    HasDerivAt (fun s => matchingPhase (-Y s 0) (Y s 2) (Y s 3))
      (matchingPhaseRate (-Y t 0) (Y t 1) (Y t 2) (Y t 3) / connectionClockRate (Y t)) t := by
  convert! hasDerivAt_matchingPhase_scaled hY hm using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionClockProjection_wall {y v : ProjectiveState} {ζ : ℝ}
    (hD : connectionClockRate y ≠ 0) (hw : y 3 ≠ 0) :
    connectionClockProjection y v ζ 3 = ζ * y 3 := by
  change v 3 - (v 3 / y 3 - ζ) * connectionLogField y 3 = _
  rw [(connectionLogField_components hD).2.2.2]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionClockProjection {β v : ℝ → ProjectiveState} {t ζ : ℝ}
    (hβ : HasDerivAt β (projectiveOriginalField (β t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (β t) (v t)) t)
    (hw : β t 3 ≠ 0) (hden : projectiveStateDenom (β t) ≠ 0)
    (hD : connectionClockRate (β t) ≠ 0) :
    HasDerivAt (fun s => connectionClockProjection (β s) (v s) ζ)
      (connectionOriginalClockRate (β t) • fderiv ℝ connectionLogField (β t)
        (connectionClockProjection (β t) (v t) ζ)) t := by
  have hF := (contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)
  have hwnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), y 3 ≠ 0 :=
    (continuous_apply 3).continuousAt.eventually_ne hw
  have hDnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), connectionClockRate y ≠ 0 :=
    (contDiff_connectionClockRate 1).continuous.continuousAt.eventually_ne hD
  have hclock : (fun y => fderiv ℝ connectionLogClock y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] connectionOriginalClockRate := by
    filter_upwards [hwnear] with y hy
    exact connectionLogClock_fderiv_field hy
  have hstate : (fun y => fderiv ℝ (id : ProjectiveState → ProjectiveState) y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] (fun y => connectionOriginalClockRate y • connectionLogField y) := by
    filter_upwards [hDnear] with y hy
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using projectiveOriginalField_connectionLog hy
  have hfield : DifferentiableAt ℝ (fun q : ℝ × ProjectiveState => connectionLogField q.2)
      (connectionLogClock (β t), β t) := by
    fun_prop
  have H := hasDerivAt_coordinate_clock_variation (p := id)
    (field := fun q : ℝ × ProjectiveState => connectionLogField q.2)
    contDiffAt_id (contDiffAt_connectionLogClock 2 hw)
    ((contDiffAt_projectiveOriginalField 1 hden).differentiableAt (by norm_num))
    ((contDiffAt_connectionOriginalClockRate 1 hden).differentiableAt (by norm_num))
    hfield hβ hv hclock hstate
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at H
  have hζ := (hF.hasFDerivAt.comp_hasDerivAt t hβ).const_smul ζ
  have heq : (fun s => connectionClockProjection (β s) (v s) ζ) =ᶠ[𝓝 t]
      (fun s => v s - fderiv ℝ connectionLogClock (β s) (v s) • connectionLogField (β s) +
        ζ • connectionLogField (β s)) := by
    filter_upwards [hβ.continuousAt.eventually hwnear] with s hs
    rw [connectionClockProjection, connectionLogClock_fderiv hs, sub_smul]
    module
  apply ((H.add hζ).congr_of_eventuallyEq heq).congr_deriv
  simp only [projectiveOriginalField_connectionLog hD, connectionClockProjection,
    connectionLogClock_fderiv hw, map_sub, map_smul]
  module

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    connectionProjectedFlowVariation y t₀ t₀ w = w := by
  rw [connectionProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]
  simp [connectionClockProjection]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => connectionProjectedFlowVariation y t₀ s w)
      (connectionOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        fderiv ℝ connectionLogField (projectiveOriginalFlow y t₀ t)
          (connectionProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_connectionClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hw
    (ne_of_gt (toProjectiveState_denom_pos hA hc)) hclock

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionProjectedFlowVariation_log {y : ProjectiveState} {t₀ z : ℝ}
    {q : ℝ → ℝ} (hD : 0 < projectiveStateDenom y)
    (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hw : projectiveOriginalFlow y t₀ (q z) 3 ≠ 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (w : ProjectiveState) :
    HasDerivAt (fun r => connectionProjectedFlowVariation y t₀ (q r) w)
      (fderiv ℝ connectionLogField (projectiveOriginalFlow y t₀ (q z))
        (connectionProjectedFlowVariation y t₀ (q z) w)) z := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ (q z)) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have H := (hasDerivAt_connectionProjectedFlowVariation hD ht hA hw hclock w).scomp z hq
  simpa only [Function.comp_def, smul_smul, one_div_mul_cancel hr, one_smul] using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionLogRates_weighted {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hmt : 1 < m t) (hf : matchingPhaseSlope (m t) (v t) (w t) ≠ 0)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionLogRates (m s) (u s) (v s) (w s))
      (fun i => ∑ j : Fin 4, connectionLogCoefficientMatrix (m t) (u t) (v t) (w t) i j * d j) t := by
  have hG := hasDerivAt_connectionPhaseG_weighted d hm hu hv hw hmt hf hD
  have hab := hasDerivAt_connection_clock_weighted_curves d hm hu hv hw hD
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLog_system {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => (![matchingPhase (-Y s 0) (Y s 2) (Y s 3),
      Real.log (Y s 1), Real.log (Y s 2)] : Fin 3 → ℝ))
      (connectionLogRates (-Y t 0) (Y t 1) (Y t 2) (Y t 3)) t := by
  have hG := hasDerivAt_matchingPhase_connectionLog hY hm
  have hab := hasDerivAt_connectionLog_amplitudes hY hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hG
  · exact hab.1
  · exact hab.2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_connectionLogCoordinates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    ContDiffAt ℝ n connectionLogCoordinates y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_matchingPhase_comp n (by fun_prop) (by fun_prop) (by fun_prop) hm
  · exact (contDiff_apply ℝ ℝ 1).contDiffAt.log hu
  · exact (contDiff_apply ℝ ℝ 2).contDiffAt.log hv
  · exact (contDiff_apply ℝ ℝ 3).contDiffAt.log hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLogCoordinates {Y : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y v t) (hm : 1 < -Y t 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogTangent (Y t) v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_matchingPhase (hasDerivAt_pi.mp hY 0).neg
      (hasDerivAt_pi.mp hY 2) (hasDerivAt_pi.mp hY 3) hm
  · exact (hasDerivAt_pi.mp hY 1).log hu
  · exact (hasDerivAt_pi.mp hY 2).log hv
  · exact (hasDerivAt_pi.mp hY 3).log hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogCoordinates_fderiv {y : ProjectiveState}
    (hm : 1 < -y 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogCoordinates y v = connectionLogTangent y v := by
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasFDerivAt connectionLogCoordinates (fderiv ℝ connectionLogCoordinates y) (y + (0 : ℝ) • v) := by
    simpa using ((contDiffAt_connectionLogCoordinates 1 hm hu hv hw).differentiableAt (by norm_num)).hasFDerivAt
  have H := hasDerivAt_connectionLogCoordinates hline (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have HD : HasDerivAt (fun s : ℝ => connectionLogCoordinates (y + s • v))
      (fderiv ℝ connectionLogCoordinates y v) 0 := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using HD.unique H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_connectionLogCoordinates_flow {Y : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t) (hm : 1 < -Y t 0)
    (hD : connectionClockRate (Y t) ≠ 0) (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinates (Y s)) (connectionLogCoordinateRates (Y t)) t := by
  have H := hasDerivAt_connectionLog_system hY hm hD hu hv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp H 0
  · exact hasDerivAt_pi.mp H 1
  · exact hasDerivAt_pi.mp H 2
  · apply ((hasDerivAt_pi.mp hY 3).log hw).congr_deriv
    rw [(connectionLogField_components hD).2.2.2, div_self hw]
    rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionLogCoordinates_fderiv_field {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    fderiv ℝ connectionLogCoordinates y (connectionLogField y) = connectionLogCoordinateRates y := by
  have hline : HasDerivAt (fun s : ℝ => y + s • connectionLogField y) (connectionLogField y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (connectionLogField y)).const_add y
  have hY : HasDerivAt (fun s : ℝ => y + s • connectionLogField y)
      (connectionLogField (y + (0 : ℝ) • connectionLogField y)) 0 := by simpa using hline
  have H1 := hasDerivAt_connectionLogCoordinates hY (by simpa using hm)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  have H2 := hasDerivAt_connectionLogCoordinates_flow hY (by simpa using hm) (by simpa using hD)
    (by simpa using hu) (by simpa using hv) (by simpa using hw)
  rw [connectionLogCoordinates_fderiv hm hu hv hw]
  simpa only [zero_smul, add_zero] using H1.unique H2

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionLog_regular_near {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    ∀ᶠ z : ProjectiveState in 𝓝 y,
      1 < -z 0 ∧ connectionClockRate z ≠ 0 ∧ z 1 ≠ 0 ∧ z 2 ≠ 0 ∧ z 3 ≠ 0 := by
  filter_upwards [(continuous_apply 0).neg.continuousAt.eventually (isOpen_Ioi.mem_nhds hm),
    (contDiff_connectionClockRate 1).continuous.continuousAt.eventually_ne hD,
    (continuous_apply 1).continuousAt.eventually_ne hu,
    (continuous_apply 2).continuousAt.eventually_ne hv,
    (continuous_apply 3).continuousAt.eventually_ne hw] with z hmz hDz huz hvz hwz
  exact ⟨hmz, hDz, huz, hvz, hwz⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionLogCoordinates_lie_eventuallyEq {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0) (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) :
    (fun z => fderiv ℝ connectionLogCoordinates z (connectionLogField z)) =ᶠ[𝓝 y]
      connectionLogCoordinateRates := by
  filter_upwards [connectionLog_regular_near hm hD hu hv hw] with z hz
  exact connectionLogCoordinates_fderiv_field hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionLogCoordinateRates {Y : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y v t) (hm : 1 < -Y t 0) (hD : connectionClockRate (Y t) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogCoordinateRates (Y s))
      (connectionLogLinearizedRates (Y t) (connectionLogTangent (Y t) v)) t := by
  let d := connectionLogTangent (Y t) v
  have hm' : HasDerivAt (fun s => -Y s 0)
      (d 0 / matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) +
        matchingPhaseVVariation (-Y t 0) (Y t 2) (Y t 3) * d 2 +
        matchingPhaseWVariation (-Y t 0) (Y t 2) (Y t 3) * d 3) t := by
    apply (hasDerivAt_pi.mp hY 0).neg.congr_deriv
    dsimp [d, connectionLogTangent, matchingPhaseVVariation, matchingPhaseWVariation]
    generalize hF : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) = F at hf ⊢
    generalize hK : phaseNorm (-Y t 0 + 1) (Y t 2) = K
    generalize hL : phaseNorm (-Y t 0 - 1) (Y t 3) = L
    field_simp
    ring
  have hwall (i : Fin 4) (hi : Y t i ≠ 0) : HasDerivAt (fun s => Y s i) (Y t i * (v i / Y t i)) t := by
    simpa only [mul_div_cancel₀ _ hi] using hasDerivAt_pi.mp hY i
  have H := hasDerivAt_connectionLogRates_weighted
    (m := fun s => -Y s 0) (u := fun s => Y s 1) (v := fun s => Y s 2) (w := fun s => Y s 3)
    (t := t) d hm' (hwall 1 hu) (hwall 2 hv) (hwall 3 hw) hm hf hD
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp H 0
  · exact hasDerivAt_pi.mp H 1
  · exact hasDerivAt_pi.mp H 2
  · exact hasDerivAt_const t (1 : ℝ)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.connectionLogCoordinateRates_fderiv {y : ProjectiveState}
    (hm : 1 < -y 0) (hD : connectionClockRate y ≠ 0)
    (hf : matchingPhaseSlope (-y 0) (y 2) (y 3) ≠ 0)
    (hu : y 1 ≠ 0) (hv : y 2 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ connectionLogCoordinateRates y v = connectionLogLinearizedRates y (connectionLogTangent y v) := by
  have hC := contDiffAt_connectionLogCoordinates 2 hm hu hv hw
  have hCD := (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := (contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)
  have hR := (hCD.hasFDerivAt.clm_apply hF.hasFDerivAt).congr_of_eventuallyEq
    (connectionLogCoordinates_lie_eventuallyEq hm hD hu hv hw).symm
  have hline : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd : HasFDerivAt connectionLogCoordinateRates (fderiv ℝ connectionLogCoordinateRates y)
      (y + (0 : ℝ) • v) := by simpa using hR.differentiableAt.hasFDerivAt
  have HD : HasDerivAt (fun s : ℝ => connectionLogCoordinateRates (y + s • v))
      (fderiv ℝ connectionLogCoordinateRates y v) 0 := by
    simpa only [Function.comp_def] using hd.comp_hasDerivAt 0 hline
  have H := hasDerivAt_connectionLogCoordinateRates hline (by simpa using hm) (by simpa using hD)
    (by simpa using hf) (by simpa using hu) (by simpa using hv) (by simpa using hw)
  simpa only [zero_smul, add_zero] using HD.unique H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_connectionLogTangent {Y v : ℝ → ProjectiveState} {t : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y t)) t)
    (hv' : HasDerivAt v (fderiv ℝ connectionLogField (Y t) (v t)) t)
    (hm : 1 < -Y t 0) (hD : connectionClockRate (Y t) ≠ 0)
    (hf : matchingPhaseSlope (-Y t 0) (Y t 2) (Y t 3) ≠ 0)
    (hu : Y t 1 ≠ 0) (hv : Y t 2 ≠ 0) (hw : Y t 3 ≠ 0) :
    HasDerivAt (fun s => connectionLogTangent (Y s) (v s))
      (connectionLogLinearizedRates (Y t) (connectionLogTangent (Y t) (v t))) t := by
  have H := hasDerivAt_observable_variation (contDiffAt_connectionLogCoordinates 2 hm hu hv hw)
    ((contDiffAt_connectionLogField 1 hD).differentiableAt (by norm_num)) hY hv'
  rw [(connectionLogCoordinates_lie_eventuallyEq hm hD hu hv hw).fderiv_eq,
    connectionLogCoordinateRates_fderiv hm hD hf hu hv hw] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [hY.continuousAt.eventually (connectionLog_regular_near hm hD hu hv hw)] with s hs
  exact (connectionLogCoordinates_fderiv hs.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 (v s)).symm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionPhaseFeedbackBudget_nonneg {μ u p : ℝ} (hμ : 0 ≤ μ) (hu : 0 ≤ u) :
    0 ≤ connectionPhaseFeedbackBudget μ u p := by
  unfold connectionPhaseFeedbackBudget
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_connectionLog {y : ProjectiveState} {t₀ z : ℝ}
    {q : ℝ → ℝ} (hD : 0 < projectiveStateDenom y)
    (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z) :
    HasDerivAt (fun r => projectiveOriginalFlow y t₀ (q r))
      (connectionLogField (projectiveOriginalFlow y t₀ (q z))) z := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ (q z)) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hr : connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (ne_of_gt (toProjectiveState_denom_pos hA hc))) hclock
  have H := (hasDerivAt_projectiveOriginalFlow_time hD ht hA).scomp z hq
  rw [projectiveOriginalField_connectionLog hclock] at H
  simpa only [Function.comp_def, smul_smul, one_div_mul_cancel hr, one_smul] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_connectionLogFlowVariation {y : ProjectiveState} {t₀ z : ℝ} {q : ℝ → ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : 1 < -projectiveOriginalFlow y t₀ (q z) 0)
    (hclock : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0)
    (hf : matchingPhaseSlope (-projectiveOriginalFlow y t₀ (q z) 0)
      (projectiveOriginalFlow y t₀ (q z) 2) (projectiveOriginalFlow y t₀ (q z) 3) ≠ 0)
    (hu : projectiveOriginalFlow y t₀ (q z) 1 ≠ 0) (hv : projectiveOriginalFlow y t₀ (q z) 2 ≠ 0)
    (hw : projectiveOriginalFlow y t₀ (q z) 3 ≠ 0)
    (hq : HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (v : ProjectiveState) :
    HasDerivAt (fun r => connectionLogFlowVariation y t₀ (q r) v)
      (connectionLogLinearizedRates (projectiveOriginalFlow y t₀ (q z))
        (connectionLogFlowVariation y t₀ (q z) v)) z :=
  hasDerivAt_connectionLogTangent (hasDerivAt_projectiveOriginalFlow_connectionLog hD ht hA hclock hq)
    (hasDerivAt_connectionProjectedFlowVariation_log hD ht hA hw hclock hq v) hm hclock hf hu hv hw

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionLogFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (v : ProjectiveState) :
    connectionLogFlowVariation y t₀ t₀ v = connectionLogTangent y v := by
  rw [connectionLogFlowVariation, projectiveOriginalFlow_initial hD, connectionProjectedFlowVariation_initial hD]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionLogFlowVariation_wall {y : ProjectiveState} {t₀ t : ℝ} (v : ProjectiveState)
    (hD : connectionClockRate (projectiveOriginalFlow y t₀ t) ≠ 0)
    (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0) :
    connectionLogFlowVariation y t₀ t v 3 = v 3 / y 3 := by
  change connectionClockProjection _ _ _ 3 / projectiveOriginalFlow y t₀ t 3 = _
  rw [connectionClockProjection_wall hD hw, mul_div_cancel_right₀ _ hw]

end
end

/-- Uniform phase and transverse bounds for the actual radial initial derivative. -/
theorem solution {y : ProjectiveState} {q : ℝ → ℝ}
    {t₀ μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ) (hden : 0 < projectiveStateDenom y)
    (hdom : ∀ z ∈ Icc a b, q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hchart : ∀ z ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : ∀ z ∈ Icc a b, |-projectiveOriginalFlow y t₀ (q z) 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1)
    (hentry : y 1 ≤ y 2) (hsmall : y 1 ≤ (1 / 10000) / μ) (hwall : y 3 ≤ 1 / 10000)
    (hq : ∀ z ∈ Icc a b,
      HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (hqa : q a = t₀) (v : ProjectiveState) (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    ∀ t ∈ Icc a b, |connectionLogFlowVariation y t₀ (q t) v 0| ≤ (16 / 15) * |v 0| ∧
      |connectionLogFlowVariation y t₀ (q t) v 0 - connectionLogTangent y v 0| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ (y 1) (y 2 * y 3) * |v 0| ∧
      ‖connectionWeightedTangent μ (connectionLogFlowVariation y t₀ (q t) v)‖ ≤
        (2048 / 15) * (t - a) * |v 0| := by
  have hu' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000 := ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hw' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1 := ⟨(hw z hz).1.le, (hw z hz).2⟩
  have hclock (z : ℝ) (hz : z ∈ Icc a b) : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu' z hz) (hv' z hz) (hw' z hz)).1
    change μ / 2 ≤ connectionClockRate (projectiveOriginalFlow y t₀ (q z)) at H
    linarith only [H, hμ]
  have hfield (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz) (hclock z hz) (hq z hz)
  have hvar (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_connectionLogFlowVariation (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) (hclock z hz)
      (by have H := (matchingPhase_slope_bounds hμ (hm z hz) (hv' z hz) (hw' z hz)).1; linarith only [H])
      (ne_of_gt (hu z hz).1) (ne_of_gt (hv z hz).1) (ne_of_gt (hw z hz).1) (hq z hz) v
  have hinit : projectiveOriginalFlow y t₀ (q a) = y := by rw [hqa, projectiveOriginalFlow_initial hden]
  have hdinit : connectionLogFlowVariation y t₀ (q a) v = connectionLogTangent y v := by
    rw [hqa, connectionLogFlowVariation_initial hden]
  have H := connectionLog_radial_variation_bounds
    (Y := fun z => projectiveOriginalFlow y t₀ (q z)) (D := fun z => connectionLogFlowVariation y t₀ (q z) v)
    hab hμ hfield hm hu' hv hw'
    (by simpa only [hinit] using hentry) (by simpa only [hinit] using hsmall) (by simpa only [hinit] using hwall) hvar
    (fun z hz => by rw [connectionLogFlowVariation_wall v (hclock z hz) (ne_of_gt (hw z hz).1), hv3, zero_div])
    (by simp [hdinit, connectionLogTangent, hv1]) (by simp [hdinit, connectionLogTangent, hv2])
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hF : 3 / 4 ≤ matchingPhaseSlope (-y 0) (y 2) (y 3) ∧
      matchingPhaseSlope (-y 0) (y 2) (y 3) ≤ 1 := by
    simpa only [hinit] using matchingPhase_slope_bounds hμ (hm a ha) (hv' a ha) (hw' a ha)
  have hF0 : 0 ≤ matchingPhaseSlope (-y 0) (y 2) (y 3) := by linarith only [hF.1]
  have hZ : |connectionLogTangent y v 0| ≤ |v 0| := by
    simp only [connectionLogTangent, Matrix.cons_val_zero, hv2, hv3, mul_zero, add_zero,
      abs_mul, abs_neg, abs_of_nonneg hF0]
    exact (mul_le_mul_of_nonneg_right hF.2 (abs_nonneg _)).trans_eq (one_mul _)
  have hu0 : 0 ≤ y 1 := by simpa only [hinit] using (hu' a ha).1
  have hB0 : 0 ≤ connectionPhaseFeedbackBudget μ (y 1) (y 2 * y 3) :=
    connectionPhaseFeedbackBudget_nonneg (by linarith only [hμ]) hu0
  intro t ht
  have Ht := H t ht
  rw [hinit, hdinit] at Ht
  refine ⟨Ht.1.trans (mul_le_mul_of_nonneg_left hZ (by norm_num)),
    Ht.2.1.trans (mul_le_mul_of_nonneg_left hZ (by positivity)), ?_⟩
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  exact Ht.2.2.trans (mul_le_mul_of_nonneg_left hZ (by positivity))

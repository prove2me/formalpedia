-- Prove2me | solution 1 for BianchiIX.coreCoordinate_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:53:38.770175+00:00
-- url     : https://prove2.me/submissions/d38feb01-7714-4146-bd4e-66be0c2eac00

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
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
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_coreRadius {m v : ℝ → ℝ} {m' v' t : ℝ}
    (hm : HasDerivAt m m' t) (hdv : HasDerivAt v v' t) (hv : 0 < v t) :
    HasDerivAt (fun s => coreRadius (m s) (v s))
      (((m t - 1) * m' + v t * v') / coreRadius (m t) (v t)) t := by
  have he : coreEnergy (m t) (v t) ≠ 0 := by unfold coreEnergy; positivity
  have hd := (((hm.sub_const 1).pow 2).add (hdv.pow 2)).sqrt he
  convert! hd using 1
  dsimp [coreRadius, coreEnergy]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_coreAngle {m v : ℝ → ℝ} {m' v' t : ℝ}
    (hm : HasDerivAt m m' t) (hdv : HasDerivAt v v' t) (hv : 0 < v t) :
    HasDerivAt (fun s => coreAngle (m s) (v s))
      (((m t - 1) * v' - v t * m') / (coreRadius (m t) (v t) * v t)) t := by
  have hd := ((hm.const_sub 1).div hdv (ne_of_gt hv)).arsinh
  convert! hd using 1
  simp only [Pi.div_apply]
  rw [coreAngle_sqrt hv]
  have hr := ne_of_gt (coreRadius_pos (m := m t) hv)
  simp only [smul_eq_mul]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

end
end

theorem solution {y : ProjectiveState} (hv : 0 < y 2) (v : ProjectiveState) :
    (fderiv ℝ toCoreAngleState y v) 0 =
        ((y 0 - 1) * v 0 + y 2 * v 2) / coreRadius (y 0) (y 2) ∧
      fderiv ℝ projectiveCoreAngle y v =
        ((y 0 - 1) * v 2 - y 2 * v 0) / (coreRadius (y 0) (y 2) * y 2) := by
  let beta : ℝ → ProjectiveState := fun s => y + s • v
  have hzero : beta 0 = y := by simp [beta]
  have hb : HasDerivAt beta v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hm := hasDerivAt_pi.mp hb 0
  have hV := hasDerivAt_pi.mp hb 2
  have hv' : 0 < beta 0 2 := by simpa only [hzero] using hv
  have hR := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hR' := hasDerivAt_pi.mp ((hzero.symm ▸ hR).comp_hasDerivAt 0 hb) 0
  have hz' := (hzero.symm ▸ hz).comp_hasDerivAt 0 hb
  constructor
  · simpa only [hzero] using hR'.unique (hasDerivAt_coreRadius hm hV hv')
  · simpa only [hzero] using hz'.unique (hasDerivAt_coreAngle hm hV hv')

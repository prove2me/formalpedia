-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreAngle_scaled
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:27:59.749254+00:00
-- url     : https://prove2.me/submissions/ba2f0a53-a4b6-4df9-b8c6-311f56e037e7

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
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

private theorem BianchiIX.coreAngle_directional {m u v w : ℝ} (hv : 0 < v) :
    ((m - 1) * activeVelocity m u v w - v * phaseVelocity m u v w) /
        (coreRadius m v * v) = coreRadius m v * coreClockFactor (coreRadius m v) u w := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  have hv0 := ne_of_gt hv
  unfold coreClockFactor
  field_simp
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  unfold phaseVelocity activeVelocity coupling
  nlinarith [he]

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

/-- A common scalar time factor is retained, so this also applies in original Einstein time. -/
theorem solution {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : 0 < β t 2) :
    HasDerivAt (fun s => coreAngle (β s 0) (β s 2))
      (a * coreRadius (β t 0) (β t 2) * coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) t := by
  have hm := hasDerivAt_pi.mp hβ 0
  have hV := hasDerivAt_pi.mp hβ 2
  have H := hasDerivAt_coreAngle hm hV hv
  convert! H using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = ((β t 0 - 1) * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) -
    β t 2 * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3))) /
      (coreRadius (β t 0) (β t 2) * β t 2)
  rw [show ((β t 0 - 1) * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) -
    β t 2 * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3))) /
      (coreRadius (β t 0) (β t 2) * β t 2) =
    a * (((β t 0 - 1) * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) -
    β t 2 * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) /
      (coreRadius (β t 0) (β t 2) * β t 2)) by ring]
  rw [coreAngle_directional hv]
  ring

-- Prove2me | solution 1 for BianchiIX.hasDerivAt_toCoreAngleState_scaled
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:32:08.966587+00:00
-- url     : https://prove2.me/submissions/21e3ff02-6ba4-43d9-ad03-d674e5a1e86d

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreAngleField_coordinates
import Theorems.Thm_BianchiIX_weak_product_directional
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

private theorem BianchiIX.coreRadius_directional {m u v w : ℝ} (hv : 0 < v) :
    ((m - 1) * phaseVelocity m u v w + v * activeVelocity m u v w) / coreRadius m v =
      -coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2 := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  apply (div_eq_iff hr).mpr
  field_simp
  rw [coreRadius_sq]
  unfold phaseVelocity activeVelocity coupling coreEnergy
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

theorem solution {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : 0 < β t 2)
    (hd : coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3) ≠ 0) :
    HasDerivAt (fun s => toCoreAngleState (β s))
      ((a * coreRadius (β t 0) (β t 2) * coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) •
        coreAngleField (coreAngle (β t 0) (β t 2)) (toCoreAngleState (β t))) t := by
  have hr := ne_of_gt (coreRadius_pos (m := β t 0) hv)
  have hm := hasDerivAt_pi.mp hβ 0
  have hu := hasDerivAt_pi.mp hβ 1
  have hV := hasDerivAt_pi.mp hβ 2
  have hw := hasDerivAt_pi.mp hβ 3
  rw [show toCoreAngleState (β t) = ![coreRadius (β t 0) (β t 2), β t 1, β t 2 * β t 3] from rfl,
    coreAngleField_coordinates hv]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hasDerivAt_coreRadius hm hV hv using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    change _ = ((β t 0 - 1) * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) +
      β t 2 * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3))) / coreRadius (β t 0) (β t 2)
    rw [show ((β t 0 - 1) * (a * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3)) +
      β t 2 * (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3))) / coreRadius (β t 0) (β t 2) =
      a * (((β t 0 - 1) * phaseVelocity (β t 0) (β t 1) (β t 2) (β t 3) +
      β t 2 * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) / coreRadius (β t 0) (β t 2)) by ring]
    rw [coreRadius_directional hv]
    dsimp
    field_simp
  · convert! hu using 1
    change _ = a * strongVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp
    field_simp
  · convert! hV.mul hw using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    change _ = a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * (a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3))
    rw [show a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * (a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)) =
      a * (activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) * β t 3 +
      β t 2 * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)) by ring]
    rw [weak_product_directional]
    dsimp
    field_simp

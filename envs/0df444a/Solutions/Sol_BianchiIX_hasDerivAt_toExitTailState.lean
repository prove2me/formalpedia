-- Prove2me | solution 1 for BianchiIX.hasDerivAt_toExitTailState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:56:09.081239+00:00
-- url     : https://prove2.me/submissions/4b537d8f-c4ef-434e-950c-9859a6719999

import Definitions.Def_BianchiIX_TerminalConnectionData
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX
open Set

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]


/-- The logarithmic tail equations are the exact pullback of the projective Einstein vector field. -/
theorem solution {β : ℝ → ProjectiveState} {t : ℝ}
    (hβ : HasDerivAt β (exitLogField (β t)) t) (hv : 0 < β t 2)
    (hm : β t 0 < 1) :
    HasDerivAt (fun s => toExitTailState (β s)) (exitTailField (β t 2) (toExitTailState (β t))) t := by
  have hg := exitTailGap_of_coreRadius (v := β t 2) hm
  have he := coreRadius_sq (β t 0) (β t 2)
  have hc := exitClockRate_tail hm
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · have H := hasDerivAt_coreRadius (hasDerivAt_pi.mp hβ 0) (hasDerivAt_pi.mp hβ 2) hv
    convert! H using 1
    change exitTailRadial (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) = _
    calc
      _ = (exitClockRate (β t))⁻¹ * (-coupling (β t 1) (β t 2) (β t 3) * coreRadius (β t 0) (β t 2) +
          (β t 0 - 1) / coreRadius (β t 0) (β t 2) * (β t 1 - β t 3) ^ 2) := by
        dsimp only [exitTailRadial]
        rw [hg, ← hc]
        ring
      _ = _ := by
        rw [← coreRadius_directional hv]
        change _ = ((β t 0 - 1) * ((exitClockRate (β t))⁻¹ * phaseVelocity _ _ _ _) +
          β t 2 * ((exitClockRate (β t))⁻¹ * activeVelocity _ _ _ _)) / _
        ring
  · have H := hasDerivAt_pi.mp hβ 1
    convert! H using 1
    change exitTailStrongRate (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) * β t 1 =
      (exitClockRate (β t))⁻¹ * strongVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp only [exitTailStrongRate, strongVelocity]
    rw [hg, ← hc, he]
    dsimp only [coreEnergy]
    ring
  · have H := hasDerivAt_pi.mp hβ 3
    convert! H using 1
    change exitTailWeakRate (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) * β t 3 =
      (exitClockRate (β t))⁻¹ * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp only [exitTailWeakRate, weakVelocity]
    rw [hg, ← hc]
    ring

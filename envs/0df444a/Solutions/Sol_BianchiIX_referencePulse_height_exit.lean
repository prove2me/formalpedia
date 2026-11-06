-- Prove2me | solution 1 for BianchiIX.referencePulse_height_exit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:27:56.025858+00:00
-- url     : https://prove2.me/submissions/a524149c-8bb4-4406-a619-e7b4a7d93550

import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Theorems.Thm_BianchiIX_referencePulse_energy
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
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

noncomputable section
open BianchiIX
open Set


theorem solution {k η : ℝ} (hk : 0 < k) (hη : 0 < η ∧ η < k) :
    referencePulse k (referenceHeightTime k η) =
      ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] := by
  let s := referenceHeightTime k η
  have hr : 1 < k / η := (one_lt_div hη.1).mpr hη.2
  have hks : k * s = Real.arcosh (k / η) := by
    dsimp [s, referenceHeightTime]
    field_simp
  have hv : referencePulse k s 2 = η := by
    change k / Real.cosh (k * s) = η
    rw [hks, Real.cosh_arcosh hr.le]
    field_simp
  have htanh : 0 < Real.tanh (k * s) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by rw [hks]; exact Real.arcosh_pos hr)) (Real.cosh_pos _)
  have hm : referencePulse k s 0 < 1 := by
    change 1 - k * Real.tanh (k * s) < 1
    linarith only [mul_pos hk htanh]
  have he := referencePulse_energy k s
  rw [hv] at he
  have hsqrt : Real.sqrt (k ^ 2 - η ^ 2) = 1 - referencePulse k s 0 :=
    (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hη.1, hη.2]) (by linarith only [hm])).mpr (by
      dsimp [coreEnergy] at he
      nlinarith only [he])
  ext i
  fin_cases i
  · change referencePulse k s 0 = 1 - Real.sqrt (k ^ 2 - η ^ 2)
    linarith only [hsqrt]
  · rfl
  · exact hv
  · rfl

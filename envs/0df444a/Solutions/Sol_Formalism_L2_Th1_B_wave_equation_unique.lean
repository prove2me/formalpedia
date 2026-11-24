-- Prove2me | solution 1 for Formalism.L2.Th1.B.wave_equation_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:32:01.330732+00:00
-- url     : https://prove2.me/submissions/ea8cc942-39ae-4ead-97a6-b109b29381b9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_coeff_evalYZero
import Theorems.Thm_Formalism_L2_Th1_B_coeff_eq_zero_of_eval_second_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
namespace Formalism.L2.Th1.B
theorem _root_.solution : WaveUnique := by
  intro K _ _ h hw h0 h1
  have hpp : ∀ (a : Fin 2) (m : Fin 2 →₀ ℕ), coeff m (pd a (pd a h)) =
      coeff (m + Finsupp.single a 2) h * (((m a : ℕ) : K) + 2) * (((m a : ℕ) : K) + 1) := by
    intro a m
    unfold pd
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    have : m + Finsupp.single a 1 + Finsupp.single a 1 = m + Finsupp.single a 2 := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [this]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  have key : ∀ j i : ℕ, coeff (Finsupp.single 0 i + Finsupp.single 1 j) h = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i
      rcases j with _ | _ | j
      · exact coeff_eq_zero_of_eval_second_zero h0 _ (by simp)
      · have := congrArg (PowerSeries.coeff i) h1
        unfold pd at this
        rw [coeff_evalYZero, map_zero, MvPowerSeries.coeff_pderiv] at this
        simpa using this
      · have e := congrArg (coeff (Finsupp.single 0 i + Finsupp.single 1 j)) hw
        rw [hpp, hpp] at e
        have e1 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (0 : Fin 2) 2
            = Finsupp.single 0 (i + 2) + Finsupp.single 1 j := by
          ext a; fin_cases a <;> simp
        have e2 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (1 : Fin 2) 2
            = Finsupp.single 0 i + Finsupp.single 1 (j + 2) := by
          ext a; fin_cases a <;> simp
        rw [e1, e2, ih j (by omega) (i + 2), zero_mul, zero_mul] at e
        have hA : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2 ≠ 0 := by
          have : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2
              = ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 + 1 : ℕ) : K) + 1 := by push_cast; ring
          rw [this]; exact Nat.cast_add_one_ne_zero _
        have hB : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        rcases mul_eq_zero.1 e.symm with e' | e'
        · rcases mul_eq_zero.1 e' with e'' | e''
          · exact e''
          · exact absurd e'' hA
        · exact absurd e' hB
  ext n
  have hn : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) := by
    ext a; fin_cases a <;> simp
  rw [hn, key, map_zero]
end Formalism.L2.Th1.B

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.coeff_PQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:55.119354+00:00
-- url     : https://prove2.me/submissions/4c2b7f19-63c7-46f9-8fdf-5a665396c025

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
theorem _root_.solution (r : ℕ) : ∀ i, i ≤ r →
    (PQ r E i).1.coeff i = 1 ∧ (∀ n, i < n → (PQ r E i).1.coeff n = 0) ∧
      (∀ n, i ≤ n → (PQ r E i).2.coeff n = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [PQ], fun n hn => ?_, fun n _ => by simp [PQ]⟩
    simp [PQ, coeff_one, Nat.pos_iff_ne_zero.mp hn]
  | succ i ih =>
    intro hi
    have h : i < r := hi
    obtain ⟨h1, h2, h3⟩ := ih h.le
    simp only [PQ, dif_pos h]
    refine ⟨?_, ?_, ?_⟩
    · rw [coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul, h1,
        h2 (i + 1) (Nat.lt_succ_self i), h3 (i + 1) (Nat.le_succ i)]
      simp
    · intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [coeff_sub, add_mul, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul,
        h2 m (by omega), h2 (m + 1) (by omega), h3 (m + 1) (by omega)]
      simp
    · intro n hn
      rw [coeff_C_mul, h2 n (by omega), mul_zero]
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation

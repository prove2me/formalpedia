-- Prove2me | solution 1 for CovecW.Hpk_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:24:53.03188+00:00
-- url     : https://prove2.me/submissions/4e90a206-cbc7-40f4-ab30-6c4953e0003c

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_sig_sig
import Theorems.Thm_CovecW_sgn_sig
import Theorems.Thm_CovecW_Hpk_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Hpk_eq]
  rw [Finset.sum_eq_single (sig k r i)]
  · rw [if_pos rfl, sig_sig, sgn_sig]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      unfold sgn
      split_ifs <;> norm_num
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · intro l _ hl
    rw [if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end CovecW

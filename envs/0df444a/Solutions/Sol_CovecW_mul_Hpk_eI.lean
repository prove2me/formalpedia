-- Prove2me | solution 1 for CovecW.mul_Hpk_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:26.262829+00:00
-- url     : https://prove2.me/submissions/89f6e268-2678-413a-843a-29d0f92edca6

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_sig_sig
import Theorems.Thm_CovecW_Hpk_eq
import Theorems.Thm_CovecW_sig_eI
import Theorems.Thm_CovecW_sig_esI
import Theorems.Thm_CovecW_sgn_esI

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
theorem _root_.solution (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (i : Fin (2 * r + k + 1)) : (M * Hpk k r) i (eI k r a) = M i (esI k r a) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [Hpk_eq, if_pos (sig_esI k r a).symm, sgn_esI, mul_one]
  · intro l _ hl
    rw [Hpk_eq, if_neg, mul_zero]
    intro h
    apply hl
    have h2 := congrArg (sig k r) h
    rw [sig_sig, sig_eI] at h2
    exact h2.symm
  · intro h
    exact absurd (Finset.mem_univ _) h
end CovecW

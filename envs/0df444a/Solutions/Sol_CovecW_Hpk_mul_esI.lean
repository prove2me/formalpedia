-- Prove2me | solution 1 for CovecW.Hpk_mul_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:23.694304+00:00
-- url     : https://prove2.me/submissions/5b5b2f62-616c-4006-8dbc-e18eb4a28418

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_Hpk_eq
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
theorem _root_.solution (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (esI k r b) j = M (eI k r b) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (esI k r b))]
  · rw [Hpk_eq, if_pos rfl, sgn_esI, sig_esI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end CovecW

-- Prove2me | solution 1 for CovecW.Hpk_mul_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:24:52.063576+00:00
-- url     : https://prove2.me/submissions/fa498fbc-d601-461c-a6e4-07daa9bafe00

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_Hpk_eq
import Theorems.Thm_CovecW_sig_eI
import Theorems.Thm_CovecW_sgn_eI

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
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (eI k r a) j = M (esI k r a) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (eI k r a))]
  · rw [Hpk_eq, if_pos rfl, sgn_eI, sig_eI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end CovecW

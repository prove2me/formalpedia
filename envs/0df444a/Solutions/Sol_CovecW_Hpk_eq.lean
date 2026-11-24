-- Prove2me | solution 1 for CovecW.Hpk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:38:02.283159+00:00
-- url     : https://prove2.me/submissions/a65a9ed2-dc50-4164-9724-165a5ab6c6ce

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_sig_val

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, sgn, Fin.ext_iff, sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)
end CovecW

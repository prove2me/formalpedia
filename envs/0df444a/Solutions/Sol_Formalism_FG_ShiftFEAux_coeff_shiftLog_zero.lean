-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.coeff_shiftLog_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:09.747618+00:00
-- url     : https://prove2.me/submissions/d0426b30-ff44-4188-a000-f1ce7b83392d

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}
namespace Formalism.FG.ShiftFEAux
theorem _root_.solution (j : ZMod m) (n : ZMod m →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) :
    coeff n (shiftLog K l m j) = 0 := by
  rw [coeff_shiftLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)
end Formalism.FG.ShiftFEAux

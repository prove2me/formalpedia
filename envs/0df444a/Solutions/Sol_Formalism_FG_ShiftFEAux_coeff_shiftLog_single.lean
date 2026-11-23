-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.coeff_shiftLog_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:34.601879+00:00
-- url     : https://prove2.me/submissions/a50a38eb-079e-49d2-8c52-f341ab63566b

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_pow_inj
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
theorem _root_.solution (hl : 2 ≤ l) (j : ZMod m) (e : ℕ) :
    coeff (Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) (shiftLog K l m j) =
      ((l : K) ^ e)⁻¹ := by
  rw [coeff_shiftLog, Finsupp.degree_single]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    exact hb (pow_inj hl this).symm
  · intro he
    exfalso; apply he
    rw [Finset.mem_range]
    have : e < (l ^ 2) ^ e := Nat.lt_pow_self (by nlinarith)
    omega
end Formalism.FG.ShiftFEAux

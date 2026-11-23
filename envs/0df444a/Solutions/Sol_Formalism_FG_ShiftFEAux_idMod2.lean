-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.idMod2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:12.27459+00:00
-- url     : https://prove2.me/submissions/edcfcb58-cd34-4eeb-af1a-462fbfda966a

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_eq_zero_of_pow_eq_one
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_single
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_zero

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
theorem _root_.solution (hl : 2 ≤ l) : IsIdMod2 (shiftLog K l m) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_shiftLog_zero
    intro e h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    have hpos : 0 < (l ^ 2) ^ e := by positivity
    have h0 : (0 : ZMod m →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega
  · by_cases hij : i = j
    · subst hij
      have := coeff_shiftLog_single (K := K) hl i 0
      simpa using this
    · rw [if_neg hij]
      apply coeff_shiftLog_zero
      intro e h
      have hd := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at hd
      have he := eq_zero_of_pow_eq_one hl hd.symm
      subst he
      apply hij
      simpa using (Finsupp.single_left_inj one_ne_zero).mp h
end Formalism.FG.ShiftFEAux

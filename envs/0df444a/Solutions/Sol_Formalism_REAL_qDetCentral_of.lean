-- Prove2me | solution 1 for Formalism.REAL.qDetCentral_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:28.572749+00:00
-- url     : https://prove2.me/submissions/69633e1b-2b88-4b6d-8d8c-b74d2774f884

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_row_eq
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_col_eq
import Theorems.Thm_Formalism_REAL_generator_commutator_quantumDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hr : QSkewRow) (hc : QSkewCol) : QDetCentral := by
  unfold QDetCentral
  intro A _ _ n E hE u c d
  have h := generator_commutator_quantumDet E hE u c d
  have key : qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u = 0 := by
    by_cases hcd : c = d
    · rw [hcd]
      have hid : Function.update (id : Fin n → Fin n) d d = id := by
        funext x
        by_cases hx : x = d
        · subst hx; simp
        · simp [hx]
      rw [hid, sub_self]
    · rw [quantumMinor_eq_zero_of_row_eq hr E (Function.update (id : Fin n → Fin n) d c) id u c d hcd
          (by simp [hcd]),
        quantumMinor_eq_zero_of_col_eq hc E hE id (Function.update (id : Fin n → Fin n) c d) u c d hcd
          (by simp [Ne.symm hcd]), sub_zero]
  rw [key, sub_eq_zero] at h
  exact h.symm
end Formalism.REAL

-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:45.73081+00:00
-- url     : https://prove2.me/submissions/05739e6f-e6a9-4ca3-9aa2-17baf0aa4256

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_eq_sum
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Finset
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W : Type*} [AddCommGroup W]
variable {H : AddSubgroup W} (hfin : ∀ k, 0 < k → Finite (Qt k H))
include hfin
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution : integ H (fun _ => (1 : ℂ)) = 1 := by
  classical
  have hinv : IsInv 1 H (fun _ => (1 : ℂ)) := fun _ _ _ _ => rfl
  rw [integ_eq hfin Nat.one_pos hinv]
  haveI := hfin _ Nat.one_pos
  letI := Fintype.ofFinite (Qt 1 H)
  rw [avg_eq_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : (Fintype.card (Qt 1 H) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact inv_mul_cancel₀ this
end Formalism.IndefR.Fin.Four

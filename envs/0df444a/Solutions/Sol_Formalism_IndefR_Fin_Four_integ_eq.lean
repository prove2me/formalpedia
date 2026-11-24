-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:02:18.784962+00:00
-- url     : https://prove2.me/submissions/d3243a7f-ae2a-4d4c-93c7-e8fae1f8c7d4

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_mul

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
theorem _root_.solution {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) : integ H g = avg k H g := by
  have h : ∃ k, 0 < k ∧ IsInv k H g := ⟨k, hk, hg⟩
  rw [integ, dif_pos h]
  obtain ⟨hk0, hg0⟩ := h.choose_spec
  haveI := hfin _ hk0
  haveI := hfin _ hk
  haveI := hfin _ (Nat.mul_pos hk0 hk)
  haveI := hfin _ (Nat.mul_pos hk hk0)
  rw [← avg_mul h.choose k H g hg0, ← avg_mul k h.choose H g hg, Nat.mul_comm]
end Formalism.IndefR.Fin.Four

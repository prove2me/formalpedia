-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:00.588665+00:00
-- url     : https://prove2.me/submissions/b5eff3c6-4325-4106-a682-82a9309445da

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_eq_sum
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_eq
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_cmul

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
theorem _root_.solution {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) (c : ℂ) :
    integ H (fun t => c * g t) = c * integ H g := by
  classical
  rw [integ_eq hfin hk (hg.cmul c), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum, ← Finset.mul_sum]
  ring
end Formalism.IndefR.Fin.Four

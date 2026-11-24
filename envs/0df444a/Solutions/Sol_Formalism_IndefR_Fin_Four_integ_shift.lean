-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.integ_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:02.661608+00:00
-- url     : https://prove2.me/submissions/f02df5dc-48fe-4055-bc7e-e099dfbdca4c

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_eq_sum
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_eq
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_shift

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
theorem _root_.solution {k : ℕ} (hk : 0 < k) {g : W → ℂ} (hg : IsInv k H g) {v : W} (hv : v ∈ H) :
    integ H (fun t => g (t + v)) = integ H g := by
  classical
  rw [integ_eq hfin hk (hg.shift hv), integ_eq hfin hk hg]
  haveI := hfin _ hk
  letI := Fintype.ofFinite (Qt k H)
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let m : Qt k H := QuotientAddGroup.mk (⟨v, hv⟩ : H)
  have key : ∀ q : Qt k H, g (((q.out : H) : W) + v) = g ((((q + m).out : H) : W)) := by
    intro q
    have h1 : q + m = QuotientAddGroup.mk (q.out + ⟨v, hv⟩) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [h1, hg.out_mk]
    rfl
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun q => rfl)
end Formalism.IndefR.Fin.Four

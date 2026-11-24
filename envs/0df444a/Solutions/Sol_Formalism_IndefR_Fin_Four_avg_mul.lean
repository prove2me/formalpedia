-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.avg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:54.05474+00:00
-- url     : https://prove2.me/submissions/49d6d3a2-c90a-4a6e-8a4c-8806e1b76ad5

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasC_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Theorems.Thm_Formalism_IndefR_Fin_Four_smulSub_mul_le
import Theorems.Thm_Formalism_IndefR_Fin_Four_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_eq_sum
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_comp_surj

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
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (k j : ℕ) (H : AddSubgroup W) [Finite (Qt k H)] [Finite (Qt (k * j) H)] (g : W → ℂ)
    (hg : IsInv k H g) : avg (k * j) H g = avg k H g := by
  classical
  let _ := Fintype.ofFinite (Qt k H)
  let _ := Fintype.ofFinite (Qt (k * j) H)
  let π : Qt (k * j) H →+ Qt k H :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id H) (by
      intro x hx
      simp only [AddSubgroup.mem_comap, AddMonoidHom.id_apply, AddSubgroup.mem_addSubgroupOf] at hx ⊢
      exact smulSub_mul_le k j H hx)
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact ⟨QuotientAddGroup.mk x, rfl⟩
  have key : ∀ q : Qt (k * j) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
    intro q
    have : π q = QuotientAddGroup.mk q.out := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    rw [this, hg.out_mk]
  rw [avg_eq_sum, avg_eq_sum]
  simp_rw [key]
  exact avg_comp_surj π hπ (fun b => g ((b.out : H) : W))
end Formalism.IndefR.Fin.Four

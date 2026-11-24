-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.finite_nsmul_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.85642+00:00
-- url     : https://prove2.me/submissions/5a5016eb-ce7a-4df6-a24b-0a54870fb01d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist

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
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {L X : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (H : AddSubgroup W) {k : ℕ} [Finite (Qt k H)]
    (htf : ∀ t : W, k • t = 0 → t = 0) : {q : W ⧸ H | k • q.out ∈ H}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun q : W ⧸ H => if hq : k • q.out ∈ H then
      (QuotientAddGroup.mk (⟨k • q.out, hq⟩ : H) : Qt k H) else 0) (Set.toFinite _) ?_
  intro q hq q' hq' heq
  have hq1 : k • q.out ∈ H := hq
  have hq2 : k • q'.out ∈ H := hq'
  simp only [dif_pos hq1, dif_pos hq2] at heq
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at heq
  simp only [smulSub, AddSubgroup.mem_map] at heq
  obtain ⟨h, hh, hh'⟩ := heq
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hh'
  have hkey : k • (-q.out + q'.out - h) = 0 := by
    rw [smul_sub, smul_add, smul_neg, hh']
    abel
  have h3 := htf _ hkey
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
  have h4 : -q.out + q'.out = h := sub_eq_zero.1 h3
  rw [h4]
  exact hh
end Formalism.IndefR.Fin.Four

-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.Ik_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.385481+00:00
-- url     : https://prove2.me/submissions/9837bae7-11ca-4cdc-bb6c-715fc0c1ae9d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_smulSub


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
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {L Y : AddSubgroup W} {k : ℕ} [Finite (Qt (k * k) (L ⊓ Y))]
    (htf : ∀ t : W, k • t = 0 → t = 0) : Finite (Ik L Y k) := by
  let f : Ik L Y k → Qt (k * k) (L ⊓ Y) := fun q => QuotientAddGroup.mk
    ⟨k • ((q.out : ↥(Yk L Y k)) : W), AddSubgroup.mem_inf.2 ⟨(mem_Yk.1 (q.out : ↥(Yk L Y k)).2).2,
      Y.nsmul_mem (mem_Yk.1 (q.out : ↥(Yk L Y k)).2).1 k⟩⟩
  refine Finite.of_injective f fun q q' h => ?_
  have h1 := QuotientAddGroup.eq.1 h
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h1
  have h2 : k • (-((q.out : ↥(Yk L Y k)) : W) + ((q'.out : ↥(Yk L Y k)) : W) - k • u) = 0 := by
    rw [smul_sub, smul_add, smul_neg, smul_smul, hux]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  have h3 := sub_eq_zero.1 (htf _ h2)
  refine (QuotientAddGroup.out_eq' q).symm.trans ((QuotientAddGroup.eq.2 ?_).trans (QuotientAddGroup.out_eq' q'))
  rw [AddSubgroup.mem_addSubgroupOf]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
  rw [h3]
  exact mem_smulSub.2 ⟨u, hu, rfl⟩
end Formalism.IndefR.Fin.Four

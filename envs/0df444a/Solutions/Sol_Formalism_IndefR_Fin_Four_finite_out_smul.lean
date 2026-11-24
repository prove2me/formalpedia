-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.finite_out_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.935664+00:00
-- url     : https://prove2.me/submissions/86fe3160-33f5-4e27-a521-fdb83b3d8833

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans


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
theorem _root_.solution (H : AddSubgroup W) {k : ℕ} [Finite (Qt (k * k) H)] (htf : ∀ t : W, k • t = 0 → t = 0) :
    {q : W ⧸ smulSub k H | k • q.out ∈ H}.Finite := by
  refine Set.finite_coe_iff.mp (Finite.of_injective
    (fun q : {q : W ⧸ smulSub k H | k • q.out ∈ H} =>
      (QuotientAddGroup.mk (⟨k • q.1.out, q.2⟩ : H) : Qt (k * k) H)) ?_)
  rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-q₁.out + q₂.out) ∈ smulSub (k * k) H := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨h, hH, hh⟩ := AddSubgroup.mem_map.mp hm
  have key : -q₁.out + q₂.out = k • h := by
    have h0 : k • (-q₁.out + q₂.out - k • h) = 0 := by
      rw [smul_sub, smul_smul]
      exact sub_eq_zero.mpr hh.symm
    exact sub_eq_zero.mp (htf _ h0)
  have e1 := QuotientAddGroup.out_eq' q₁
  have e2 := QuotientAddGroup.out_eq' q₂
  refine Subtype.ext (e1.symm.trans (Eq.trans ?_ e2))
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact AddSubgroup.mem_map_of_mem _ hH)
end Formalism.IndefR.Fin.Four

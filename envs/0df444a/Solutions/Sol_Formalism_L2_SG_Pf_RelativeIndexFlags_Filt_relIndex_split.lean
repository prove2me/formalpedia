-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:36.811123+00:00
-- url     : https://prove2.me/submissions/8b25d646-e42d-4966-ba23-c5541852732a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_relIndex_eq_of_mul
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_inf_relIndex_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by
  have e1 := Subgroup.relIndex_inf_mul_relIndex H (H ⊔ N) X
  rw [show H ⊓ (H ⊔ N) = H from inf_of_le_left le_sup_left] at e1
  have e2 : (H ⊔ N).relIndex X = (H ⊔ N).relIndex (X ⊔ N) := by
    refine relIndex_eq_of_mul _ _ _ le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_right).1 hy
    exact ⟨x, hx, z, Subgroup.mem_sup_right hz, rfl⟩
  have e3 : H.relIndex (X ⊓ N) = H.relIndex ((H ⊔ N) ⊓ X) := by
    refine relIndex_eq_of_mul _ _ _ ?_ ?_
    · intro y hy
      exact ⟨Subgroup.mem_sup_right hy.2, hy.1⟩
    · intro y hy
      obtain ⟨h, hh, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).1 hy.1
      refine ⟨y * h⁻¹, ⟨X.mul_mem hy.2 (X.inv_mem (hHX hh)), ?_⟩, h, hh, by group⟩
      rw [← hyz]
      have : h * z * h⁻¹ ∈ N := hN.conj_mem z hz h
      simpa [mul_assoc] using this
  rw [← e1, ← e3, e2, inf_relIndex_of_le H N (X ⊓ N) inf_le_right]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsSB.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:46.066634+00:00
-- url     : https://prove2.me/submissions/8ac183e4-f684-459d-9574-0cef77d362d7

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr


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
namespace IsSB
theorem _root_.solution {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') : IsSB L X (Φ + Φ') := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨hs', k', hk', hi', hl'⟩ := h'
  have hor : ∀ t, (Φ + Φ') t ≠ 0 → Φ t ≠ 0 ∨ Φ' t ≠ 0 := by
    intro t ht
    by_contra hc
    push_neg at hc
    apply ht
    simp [hc.1, hc.2]
  refine ⟨fun t ht => (hor t ht).elim (hs t) (hs' t), k * k', Nat.mul_pos hk hk', fun u hu t => ?_,
    fun t ht => ?_⟩
  · have h1 : (k * k') • u = k • (k' • u) := (smul_smul k k' u).symm
    have h2 : (k * k') • u = k' • (k • u) := by rw [mul_comm]; exact (smul_smul k' k u).symm
    simp only [Pi.add_apply]
    congr 1
    · rw [h1]; exact hi _ ((L ⊓ X).nsmul_mem hu k') t
    · rw [h2]; exact hi' _ ((L ⊓ X).nsmul_mem hu k) t
  · rcases hor t ht with h0 | h0
    · rw [mul_comm, ← smul_smul]; exact L.nsmul_mem (hl t h0) k'
    · rw [← smul_smul]; exact L.nsmul_mem (hl' t h0) k
end IsSB
end Formalism.IndefR.Fin.Four

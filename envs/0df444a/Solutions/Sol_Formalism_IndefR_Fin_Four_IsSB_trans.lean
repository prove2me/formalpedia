-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsSB.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:26.034751+00:00
-- url     : https://prove2.me/submissions/a780257d-5958-48e2-be26-682a36ec7c79

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
namespace IsSB
theorem _root_.solution (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) {Φ : W → ℂ} (h : IsSB L X Φ) {x : W}
    (hx : x ∈ X) : IsSB L X (fun t => Φ (t + x)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  obtain ⟨k2, hk2, hx2⟩ := hoX x hx
  refine ⟨fun t ht => ?_, k * k2, Nat.mul_pos hk hk2, fun u hu t => ?_, fun t ht => ?_⟩
  · have h1 := hs _ ht
    simpa using X.sub_mem h1 hx
  · show Φ (t + (k * k2) • u + x) = Φ (t + x)
    rw [← smul_smul, add_right_comm]
    exact hi _ ((L ⊓ X).nsmul_mem hu k2) _
  · have h1 := hl _ ht
    have h2 : (k * k2) • t = k2 • (k • (t + x)) - k • (k2 • x) := by
      simp only [smul_add, smul_smul]
      rw [mul_comm k2 k]
      abel
    rw [h2]
    exact L.sub_mem (L.nsmul_mem h1 k2) (L.nsmul_mem hx2 k)
end IsSB
end Formalism.IndefR.Fin.Four

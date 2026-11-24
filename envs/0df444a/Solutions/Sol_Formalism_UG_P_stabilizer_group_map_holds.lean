-- Prove2me | solution 1 for Formalism.UG.P.stabilizer_group_map_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:47.478519+00:00
-- url     : https://prove2.me/submissions/7592c702-f8de-48a1-a39c-c1df9b9ba5be

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Theorems.Thm_P2M_Formalism_UG_P_glEquiv_apply__d9aedd7a5d31

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.StabGmap := by
  intro K _ R _ _ n _ _ Λ g
  unfold Formalism.UG.stabGL HermitianLatticesTheory.gmap
  show (∀ x : n → K, x ∈ Λ ↔ (g : Matrix n n K) *ᵥ x ∈ Λ) ↔ _
  constructor
  · intro hg
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Formalism.UG.glEquiv g x ∈ Λ
      rw [glEquiv_apply']
      exact (hg x).mp hx
    · intro hy
      refine ⟨(Formalism.UG.glEquiv g).symm y, ?_, ?_⟩
      · rw [hg, ← glEquiv_apply']
        simpa using hy
      · show Formalism.UG.glEquiv g ((Formalism.UG.glEquiv g).symm y) = y
        simp
  · intro hg x
    constructor
    · intro hx
      rw [← hg, Submodule.mem_map]
      exact ⟨x, hx, glEquiv_apply' g x⟩
    · intro hx
      rw [← hg, Submodule.mem_map] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzx' : Formalism.UG.glEquiv g z = (g : Matrix n n K) *ᵥ x := hzx
      have hzx'' : Formalism.UG.glEquiv g z = Formalism.UG.glEquiv g x := by
        rw [hzx', glEquiv_apply']
      rw [← (Formalism.UG.glEquiv g).injective hzx'']
      exact hz
end Formalism.UG.P

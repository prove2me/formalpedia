-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachCol_lift_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:13.561383+00:00
-- url     : https://prove2.me/submissions/7acca4ac-c251-4ae9-b00d-3cacdb6686d8

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {O X H : Type} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup H] [Module O H]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) (a : O) :
    (∀ m ∈ N, a • m ∈ I) ↔ ∀ x ∈ Hf, a • x ∈ S := by
  have key : ∀ n : N, (a • (n : X) ∈ I ↔ a • f n ∈ S) := by
    intro n
    have h := SetLike.ext_iff.mp hI (a • n)
    simpa using h
  constructor
  · intro h x hx
    rw [← hr] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (key n).mp (h n n.2)
  · intro h m hm
    exact (key ⟨m, hm⟩).mpr (h _ (by rw [← hr]; exact LinearMap.mem_range_self f _))
end Formalism.WeaklyAdmissibleFiltrations

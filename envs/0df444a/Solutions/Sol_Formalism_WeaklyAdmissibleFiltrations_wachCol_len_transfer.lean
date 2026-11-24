-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.wachCol_len_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:11.960871+00:00
-- url     : https://prove2.me/submissions/f6682373-832b-49b8-b844-16d1279ebb54

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
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) :
    Module.length O (↥N ⧸ I.comap N.subtype) = Module.length O (↥Hf ⧸ S.comap Hf.subtype) := by
  let g : N →ₗ[O] Hf := LinearMap.codRestrict Hf f (fun x => by rw [← hr]; exact LinearMap.mem_range_self f x)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hr] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let q : N →ₗ[O] (↥Hf ⧸ S.comap Hf.subtype) := (S.comap Hf.subtype).mkQ ∘ₗ g
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hg
  have hk : LinearMap.ker q = I.comap N.subtype := by
    ext x
    rw [hI, LinearMap.mem_ker, Submodule.mem_comap]
    simp [q, g]
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq
end Formalism.WeaklyAdmissibleFiltrations

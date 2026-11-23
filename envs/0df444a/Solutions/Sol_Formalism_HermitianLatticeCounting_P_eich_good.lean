-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.eich_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:01.931803+00:00
-- url     : https://prove2.me/submissions/52b4cb80-2d50-4f48-90c4-3b04010d8303

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_jointSpan_isotropicMeet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eich_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicMeet_le_jointSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hE : Formalism.HermitianLatticeCounting.S6.EichlerIsom) (F F' : FlagD H r) {x v : V} {c : K} (hx : x ∈ II F F')
    (hv : ∀ y ∈ V0 F F', H.B y v = 0) (hc : c + star c = -H.B v v) : GoodMap F F' (eich H x v c) := by
  have hxI : x ∈ F.X := (Submodule.mem_inf.1 hx).1
  have hxx : H.B x x = 0 := (X_iso F) hxI hxI
  have hxv : H.B x v = 0 := hv x (isotropicMeet_le_jointSpan F F' hx)
  obtain ⟨hiso, hl, hr⟩ := hE _ _ H x v c hxx hxv hc
  unfold GoodMap
  refine ⟨hiso, ⟨fun y y' h => ?_, fun y => ⟨_, hr y⟩⟩, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← hl y, h, hl y']
  · have h1 := hv y hy
    have h2 := pairing_jointSpan_isotropicMeet F F' hx y hy
    rw [eich_apply, h1, h2]
    simp
  · have h2 : H.B y x = 0 := B_swap0 H (hy x hx)
    rw [eich_apply, h2]
    simp only [zero_smul, sub_zero, smul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hx
end Formalism.HermitianLatticeCounting.P

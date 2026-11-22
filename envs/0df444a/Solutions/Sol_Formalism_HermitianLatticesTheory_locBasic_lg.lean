-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:42.442537+00:00
-- url     : https://prove2.me/submissions/5bdda8d2-753d-4fde-9a23-84c0e8a95f96

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (S : Ideal R → Submonoid R)
    (hS : ∀ p : Ideal R, p.IsMaximal → ∀ s ∈ S p, s ∉ p) (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ locS (S p) L) : x ∈ L := by
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R W x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ L := fun r => by simp [I]
  by_contra hxL
  have hne : I ≠ ⊤ := by
    intro h
    apply hxL
    have h1 : (1 : R) ∈ I := by
      rw [h]
      exact Submodule.mem_top
    simpa using (hI 1).mp h1
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (hx p hp)
  exact hS p hp s hs (hIp ((hI s).mpr hsx))
end Formalism.HermitianLatticesTheory

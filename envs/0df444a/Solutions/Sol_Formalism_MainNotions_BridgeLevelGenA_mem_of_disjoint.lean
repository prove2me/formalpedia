-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenA.mem_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:59.448298+00:00
-- url     : https://prove2.me/submissions/515583a7-9042-4f7c-912a-ad128e3a3f9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
namespace Formalism.MainNotions.BridgeLevelGenA
theorem _root_.solution (g : R) {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hd : Disjoint (coprS g : Set R) (P : Set R)) : g ∈ P := by
  by_contra hgP
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have htop : P ⊔ Ideal.span {g} = ⊤ := by
    by_contra h
    have e := hmax.eq_of_le h le_sup_left
    apply hgP
    rw [e]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : R) ∈ P ⊔ Ideal.span {g})
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  by_cases ha0 : a = 0
  · subst ha0
    have hco : IsCoprime p g := ⟨0, d, by simpa using hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, hp0⟩ hp
  · have hco : IsCoprime a g := ⟨1, d, by rw [one_mul]; exact hac⟩
    exact Set.disjoint_left.1 hd ⟨hco, ha0⟩ ha
end Formalism.MainNotions.BridgeLevelGenA

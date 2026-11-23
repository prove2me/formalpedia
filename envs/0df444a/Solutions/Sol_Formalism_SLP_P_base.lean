-- Prove2me | solution 1 for Formalism.SLP.P.base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:40.40713+00:00
-- url     : https://prove2.me/submissions/32908281-6eea-4228-a124-ead98363499a

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup
namespace Formalism.SLP.P
theorem _root_.solution : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.Finite ∧
    {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.ncard ≤ j ^ 0 := by
  intro j _
  have htop : ∀ H : AddSubgroup (Fin 0 → ℤ), H = ⊤ := fun H =>
    eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 0]; exact H.zero_mem
  have hsub : {H : AddSubgroup (Fin 0 → ℤ) | H.index = j} ⊆ {⊤} := fun H _ => htop H
  refine ⟨(Set.finite_singleton _).subset hsub, ?_⟩
  rw [pow_zero]
  exact (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (Set.ncard_singleton _).le
end Formalism.SLP.P

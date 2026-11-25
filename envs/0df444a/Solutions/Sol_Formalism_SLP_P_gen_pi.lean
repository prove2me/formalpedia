-- Prove2me | solution 1 for Formalism.SLP.P.gen_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:21:09.550138+00:00
-- url     : https://prove2.me/submissions/6e1361f5-2c06-4465-9093-8a33a93954b8

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
theorem _root_.solution (n : ℕ) (K : AddSubgroup (Fin n → ℤ)) :
    ∃ v : Fin n → (Fin n → ℤ), AddSubgroup.closure (Set.range v) = K := by
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) K.toIntSubmodule
  have hk : k ≤ n := by
    have h1 := Submodule.finrank_le K.toIntSubmodule
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h1
  refine ⟨fun i => if h : i.val < k then (b ⟨i, h⟩ : Fin n → ℤ) else 0, ?_⟩
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs
    · exact (b _).2
    · exact Submodule.zero_mem _
  · intro x hx
    have h2 : x ∈ (Submodule.span ℤ (Set.range b)).map K.toIntSubmodule.subtype :=
      ⟨⟨x, hx⟩, by rw [b.span_eq]; trivial, rfl⟩
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    refine ⟨⟨m, lt_of_lt_of_le m.2 hk⟩, ?_⟩
    simp [m.2]
end Formalism.SLP.P

-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.dualBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:03.833366+00:00
-- url     : https://prove2.me/submissions/18de41a7-7cc5-45ee-b93f-9d0c645c1f7a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual

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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : DualBasic := by
  intro R K V _ _ _ _ _ _ _ _ h hs hst
  have anti : ∀ L M : Submodule R V, L ≤ M → dual h M ≤ dual h L := by
    intro L M hLM x hx
    rw [dualBasic_mem_dual] at hx ⊢
    exact fun y hy => hx y (hLM hy)
  have starOne : ∀ z : K, z ∈ (1 : Submodule R K) → star z ∈ (1 : Submodule R K) := by
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hz
    obtain ⟨t, ht⟩ := hst r
    exact Submodule.mem_one.2 ⟨t, ht⟩
  have integ : ∀ L : Submodule R V, IsIntegralLat h L ↔ L ≤ dual h L := by
    intro L
    constructor
    · intro hL x hx
      rw [dualBasic_mem_dual]
      exact fun y hy => hL y hy x hx
    · intro hL x hx y hy
      exact (dualBasic_mem_dual h L y).1 (hL hy) x hx
  refine ⟨anti, ?_, ?_, integ, ?_⟩
  · intro L x hx
    rw [dualBasic_mem_dual]
    intro y hy
    have h1 : h x y ∈ (1 : Submodule R K) := (dualBasic_mem_dual h L y).1 hy x hx
    have h2 := starOne _ h1
    have h3 := hs.eq x y
    simp only [starRingEnd_apply] at h3
    rwa [h3] at h2
  · intro L M
    apply le_antisymm
    · exact le_inf (anti _ _ le_sup_left) (anti _ _ le_sup_right)
    · intro x hx
      obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.1 hx
      rw [dualBasic_mem_dual] at hxL hxM ⊢
      intro y hy
      obtain ⟨l, hl, m, hm, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      exact add_mem (hxL l hl) (hxM m hm)
  · intro L
    rw [IsUnimodular, integ, le_antisymm_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
end Formalism.HermitianLatticesTheory

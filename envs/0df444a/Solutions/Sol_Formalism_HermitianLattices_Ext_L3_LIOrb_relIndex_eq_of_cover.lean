-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.relIndex_eq_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:29.115485+00:00
-- url     : https://prove2.me/submissions/0b4330d9-cfed-477f-9f77-56a577b2d2f2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
open Subgroup
variable {G : Type*} [Group G]
private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]
end Formalism.HermitianLattices.Ext.L3.LIOrb
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
open Subgroup
variable {G : Type*} [Group G]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩
end Formalism.HermitianLattices.Ext.L3.LIOrb

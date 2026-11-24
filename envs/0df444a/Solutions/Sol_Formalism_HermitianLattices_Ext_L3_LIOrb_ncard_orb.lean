-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.ncard_orb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:24:45.397458+00:00
-- url     : https://prove2.me/submissions/f0e4cf65-00e0-470d-bd38-da26a2cbe30c

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
theorem _root_.solution {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y
end Formalism.HermitianLattices.Ext.L3.LIOrb

-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.orbCount_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:17.425389+00:00
-- url     : https://prove2.me/submissions/5ffbcbcb-58e7-43f8-8f69-1c40c9b20906

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) :
    orbCount h A B = (autSub h B).relIndex (autSub h A) := by
  let _ : MulAction (V ≃ₗ[K] V) (Submodule (𝓞 K) V) :=
    { smul := fun g L => Formalism.HermitianLatticesTheory.gmap g L
      one_smul := autSub_gmap_one
      mul_smul := autSub_gmap_mul }
  have hst : MulAction.stabilizer ↥(autSub h A) B = (autSub h B).subgroupOf (autSub h A) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      exact ⟨g.2.1, hg⟩
    · intro hg
      exact hg.2
  rw [Subgroup.relIndex, ← hst, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ B)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro C
  constructor
  · rintro ⟨g, hg, hA, hB⟩
    exact ⟨⟨g, hg, hA⟩, hB⟩
  · rintro ⟨⟨g, hg, hA⟩, hB⟩
    exact ⟨g, hg, hA, hB⟩
end Formalism.HermitianLattices.Ext.L3.LIOrb

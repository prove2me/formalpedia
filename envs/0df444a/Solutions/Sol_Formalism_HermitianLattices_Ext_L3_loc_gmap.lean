-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.loc_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:28.510588+00:00
-- url     : https://prove2.me/submissions/f4e258dd-715a-4545-b6df-07baa4a22864

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
  have hsm : ∀ (s : 𝓞 K) (v : V), g (s • v) = s • g v := fun s v => by
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s (g v), map_smul]
  unfold Formalism.HermitianLatticesTheory.loc Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.locS
  ext x
  simp only [Submodule.mem_map, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    refine ⟨g.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have e : s • g.symm x = y := g.injective (by rw [hsm, g.apply_symm_apply]; exact hyx.symm)
    rw [e]; exact hy
  · rintro ⟨z, ⟨s, hs, hz⟩, rfl⟩
    exact ⟨s, hs, s • z, hz, hsm s z⟩
end Formalism.HermitianLattices.Ext.L3

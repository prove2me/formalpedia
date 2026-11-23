-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.gmap_mem_genus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:20.496076+00:00
-- url     : https://prove2.me/submissions/f17e1eca-c606-4580-bce9-aaefeb271fba

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_loc_gmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · constructor
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact hLat.fg.map _
    · unfold Formalism.HermitianLatticesTheory.gmap
      rw [Submodule.map_coe]
      show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr g.surjective]
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]
end Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives

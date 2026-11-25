-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.exists_pairReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:55:04.092058+00:00
-- url     : https://prove2.me/submissions/18037349-6e16-46e8-a67f-aa918c818466

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_finite_rep
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_classReps
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbSum_exists_reps_of_cover
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_pairs_stable


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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1 n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices

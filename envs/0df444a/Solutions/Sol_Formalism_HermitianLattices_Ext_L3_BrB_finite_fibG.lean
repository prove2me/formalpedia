-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrB.finite_fibG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:55.221511+00:00
-- url     : https://prove2.me/submissions/057d1fe5-29dd-4d8f-84c5-2c38031bcb04

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_finite_between
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_UnimodularLocalization_nondegenerate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_isLattice_adjoin_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_le_dual_of_mem


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.BrB
theorem _root_.solution (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'} (hΛ' : Submodule.IsLattice K Λ') : (fibG S L Λ').Finite := by
  have hN := (S.isLattice_adjoin_iff Λ').2 hΛ'
  have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (UnimodularLocalization.nondegenerate hd)
    Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
  by_cases hne : (fibG S L Λ').Nonempty
  · have key : ∀ Λ ∈ fibG S L Λ', S.adjoin Λ' ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin Λ') := by
      rintro Λ ⟨hg, hx, hc⟩
      have hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ :=
        ((Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).2.2 L Λ hL.fg hg.1.fg
          hg.2).2.mp hLi
      have := S.le_dual_of_mem hs hΛi hx
      rwa [hc] at this
    obtain ⟨Λ, hΛ⟩ := hne
    exact (finite_between hN hD ((key Λ hΛ).1.trans (key Λ hΛ).2)).subset key
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty
end Formalism.HermitianLattices.Ext.L3.BrB

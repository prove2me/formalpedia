-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_fibReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:40.995946+00:00
-- url     : https://prove2.me/submissions/54284373-91d0-4984-9e47-8577fae42eda

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_pair_mem_of_fibG
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_move
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_fibG_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbSum_exists_reps_of_cover
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_gmap_res
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitBAux_res_mem_isom
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_pairReps
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_exists_smul_iff


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
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open StabilizerLattices SplitBAux
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : ∃ s', IsFibReps S L s' := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  choose γ hγ using exists_move hK hs hd S L
  obtain ⟨T, hT1, hT2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h')
    {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty}
    (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩)
    ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) V × V)))
    (sX.finite_toSet.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (hγ p (hsX p hp)).2⟩)
    (by
      rintro Λ' ⟨Λ, hΛ⟩
      obtain ⟨t, ⟨ht, k, hk⟩, -⟩ := hX _ (pair_mem_of_fibG S hΛ).1
      refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
      have e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀) := by
        rw [← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
      have := gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1
      rw [hΛ.2.2] at this
      exact ⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)
  refine ⟨T, hT1, fun Λ' hΛ' => ?_⟩
  have := hT2 Λ' hΛ'
  simp_rw [exists_smul_iff] at this
  exact this
end Formalism.HermitianLattices.Ext.L3

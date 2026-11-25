-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.pair_mem_of_fibG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:45:13.559855+00:00
-- url     : https://prove2.me/submissions/a1969b65-1a92-4df4-89aa-159bf7305b4c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_inf_perpO


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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
open SplitBAux
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ') :
    (Λ, S.x₀) ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h (Λ, S.x₀) = (emb S Λ', S.x₀) :=
  ⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices

-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.fibG_of_pair_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:21:14.002149+00:00
-- url     : https://prove2.me/submissions/35989546-80df-465d-8fba-79859ce79f81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumOrbitsEquivariant
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_emb_injective
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
    {p : Submodule (𝓞 K) V × V} (hp : p ∈ pairs h L (h S.x₀ S.x₀))
    (e : proj h p = (emb S Λ', S.x₀)) : p.1 ∈ fibG S L Λ' ∧ p.2 = S.x₀ := by
  obtain ⟨Λ, x⟩ := p
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  change Λ ⊓ perpO h x = emb S Λ' at e1
  change x = S.x₀ at e2
  subst e2
  rw [inf_perpO] at e1
  exact ⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices

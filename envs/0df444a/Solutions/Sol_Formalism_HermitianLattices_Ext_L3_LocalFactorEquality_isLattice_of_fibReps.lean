-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalFactorEquality.isLattice_of_fibReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:15.876414+00:00
-- url     : https://prove2.me/submissions/09fa13f9-baf9-4958-80c1-040985726b66

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_isLattice_cut


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits
namespace Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
theorem _root_.solution (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s') {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Λ' ∈ s') : Submodule.IsLattice K Λ' := by
  obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'
  exact StabilizerLattices.isLattice_cut S hΛ.1
end Formalism.HermitianLattices.Ext.L3.LocalFactorEquality

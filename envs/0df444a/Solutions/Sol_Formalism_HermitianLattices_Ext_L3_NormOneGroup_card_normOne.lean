-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormOneGroup.card_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:49.742604+00:00
-- url     : https://prove2.me/submissions/c45cdd1b-12eb-41cc-93f7-9b8ae1037f06

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormOneGroup
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup
theorem _root_.solution (Q : Ideal (𝓞 K)) :
    Nat.card {z : 𝓞 K ⧸ Q // NormOne Q z} = normRepCount K Q 1 1 := by
  unfold normRepCount
  refine Nat.card_congr ((Equiv.funUnique (Fin 1) (𝓞 K ⧸ Q)).symm.subtypeEquiv ?_)
  intro z
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨fun _ => y, fun i => by simpa using h1, by simpa using h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y 0, by simpa using h1 0, by simpa using h2⟩
end Formalism.HermitianLattices.Ext.L3.NormOneGroup

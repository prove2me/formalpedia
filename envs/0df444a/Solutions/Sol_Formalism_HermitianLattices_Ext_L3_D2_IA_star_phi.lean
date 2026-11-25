-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.IA.star_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:10.897634+00:00
-- url     : https://prove2.me/submissions/a3d2ac71-9a37-4329-b46a-e2f47e40c3ed

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_IA_phi_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2 Formalism.HermitianLattices.Ext.L3.D2.IA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2.IA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]
end Formalism.HermitianLattices.Ext.L3.D2.IA

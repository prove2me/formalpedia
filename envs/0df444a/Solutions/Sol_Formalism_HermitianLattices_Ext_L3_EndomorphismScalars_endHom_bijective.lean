-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.EndomorphismScalars.endHom_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:23.895843+00:00
-- url     : https://prove2.me/submissions/0178736a-2ec6-4b88-9d98-6a719881d589

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_end_surj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_EndomorphismScalars_endHom_mk

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}
namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [endHom_mk, end_eq_zero_iff h𝔭 he k] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro X
    obtain ⟨b, hb⟩ := end_surj h𝔭 he k X
    exact ⟨Ideal.Quotient.mk _ b, by rw [endHom_mk, hb]⟩
end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

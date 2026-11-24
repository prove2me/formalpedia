-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormOneGroup.normOne_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:51.82472+00:00
-- url     : https://prove2.me/submissions/48bd177b-8aec-4ed5-a8f8-60206cef6451

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_conjO_mem_extP


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormOneGroup
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j : ℕ) (b : 𝓞 K) :
    NormOne (extP K 𝔭 ^ j) (Ideal.Quotient.mk _ b) ↔ conjO K b * b - 1 ∈ extP K 𝔭 ^ j := by
  constructor
  · rintro ⟨y, hy, h1⟩
    rw [Ideal.Quotient.eq] at hy h1
    have hyb : conjO K (y - b) ∈ extP K 𝔭 ^ j := conjO_mem_extP hF 𝔭 j hy
    have e : conjO K b * b - 1 =
        (conjO K y * y - 1) - (conjO K y * (y - b) + conjO K (y - b) * b) := by
      rw [map_sub]
      ring
    rw [e]
    exact sub_mem h1 (add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hyb))
  · intro h
    exact ⟨b, rfl, Ideal.Quotient.eq.mpr h⟩
end Formalism.HermitianLattices.Ext.L3.NormOneGroup

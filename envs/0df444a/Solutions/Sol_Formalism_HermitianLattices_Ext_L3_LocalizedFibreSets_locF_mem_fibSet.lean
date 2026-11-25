-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets.locF_mem_fibSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:32.770202+00:00
-- url     : https://prove2.me/submissions/7424ecdd-da13-463c-b3e0-5be93adf0c9e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinIntegralOfNonempty
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_cut_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_locF_idem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L Λ : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'} (hΛ : Λ ∈ fibG S L Λ') {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibSet S L 𝔭 Λ' := by
  obtain ⟨⟨-, hgen⟩, hx, hc⟩ := hΛ
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 K)
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       have := congrArg (fun z : 𝓞 K => (z : K)) hab
       simpa using this)
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine ⟨locF_idem 𝔭 Λ, ?_, le_locF 𝔭 Λ hx, ?_⟩
  · obtain ⟨g, hg, e⟩ := hgen P hP
    refine ⟨g, hg, ?_⟩
    rw [← hPc, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact e
  · rw [cut_locF, hc]
end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets

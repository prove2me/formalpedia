-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.finite_vd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:48.859976+00:00
-- url     : https://prove2.me/submissions/1c7df1d8-1a89-470d-9f4e-48c0edda4851

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_discrIdeal_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_vd_eq_zero_of_not_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over


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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vd h L 𝔭.1 ≠ 0}.Finite := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  refine ((Ideal.finite_factors hD').image (fun v =>
    (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
  intro 𝔭 h𝔭
  have hle : discrIdeal h L ≤ extP K 𝔭.1 := by
    by_contra hn
    exact h𝔭 (LocF.vd_eq_zero_of_not_le hn)
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have h2 : extP K 𝔭.1 ≤ P := by
    rw [← hP𝔭]
    exact Ideal.map_comap_le
  have h1 : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭.1 := by
    rw [← hP𝔭]
    exact Ideal.comap_mono (hle.trans h2)
  have hne : 𝔭.1 ≠ ⊥ := fun e => hD' (eq_bot_iff.mpr (e ▸ h1))
  exact ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, Ideal.dvd_iff_le.mpr h1, rfl⟩
end Formalism.HermitianLattices.Ext.L3

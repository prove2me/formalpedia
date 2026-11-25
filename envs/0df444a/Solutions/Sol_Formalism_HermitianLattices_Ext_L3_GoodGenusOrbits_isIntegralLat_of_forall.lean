-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.isIntegralLat_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:01.595919+00:00
-- url     : https://prove2.me/submissions/b5477179-72b3-4cfa-8f02-d92864d94819

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_le_locF


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms SplitBAux
namespace Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, IsIntegralAt 𝔭.1 h₀ (locF 𝔭.1 M)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h₀ M := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  exact fun 𝔭 => H 𝔭 x (LocF.le_locF _ _ hx) y (LocF.le_locF _ _ hy)
end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

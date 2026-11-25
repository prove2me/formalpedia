-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.sameGenus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:45.517494+00:00
-- url     : https://prove2.me/submissions/dc597a73-80f2-419c-92d7-df33090389ed

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalizedFibreSets_exists_max_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_locF_eq_loc


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
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.SameGenus h A B ↔ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 A) = locF 𝔭.1 B := by
  constructor
  · rintro H ⟨𝔭, h𝔭⟩
    obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact H P hP
  · intro H P hP
    have hm : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have := H ⟨_, hm⟩
    rwa [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP] at this
end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

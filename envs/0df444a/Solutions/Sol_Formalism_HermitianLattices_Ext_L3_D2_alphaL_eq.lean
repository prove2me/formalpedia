-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.alphaL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:28.336596+00:00
-- url     : https://prove2.me/submissions/4ef6db08-f490-4eee-8d98-ddd53666dae4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_akCount_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_alphaL_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_akCount_locF


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, alphaL h (locF 𝔭 A₀) 𝔭 =
      (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  refine ⟨2 * vd h A₀ 𝔭 + 1, fun k hk => ?_⟩
  have h1 : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    simp_rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  rw [h1, akCount_locF hF h A₀ 𝔭 h𝔭]
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭 hk
end Formalism.HermitianLattices.Ext.L3.D2

-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.akCount_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:43.815795+00:00
-- url     : https://prove2.me/submissions/52f723b6-021f-4a98-8647-0c67bd0dd387

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_index_eq_card
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_redEnd_eq_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_redEnd_cond
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_RedC_exists_redEnd_eq

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
    ∃ k₀ : ℕ, ∀ k ≥ k₀, akCount h (locF 𝔭 A₀) 𝔭 k =
      (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) := by
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1, fun k hk => ?_⟩
  symm
  unfold akCount Subgroup.relIndex
  refine RedC.index_eq_card _
    (fun X : ↥(sSub h (locF 𝔭 A₀) 𝔭 k) => ⟨RedC.redEnd (locF 𝔭 A₀) 𝔭 k X.1 X.2.1,
      RedC.redEnd_cond hF hA₀i h𝔭 X.2⟩) ?_ ?_
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX, e⟩ := RedC.exists_redEnd_eq hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
    exact ⟨⟨X, hX⟩, Subtype.ext e⟩
  · intro a b
    rw [Subtype.mk.injEq, RedC.redEnd_eq_iff, Subgroup.mem_subgroupOf]
    rfl
end Formalism.HermitianLattices.Ext.L3.D2

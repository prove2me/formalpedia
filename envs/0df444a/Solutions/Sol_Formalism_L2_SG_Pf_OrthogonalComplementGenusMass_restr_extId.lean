-- Prove2me | solution 1 for Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.restr_extId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:51.428503+00:00
-- url     : https://prove2.me/submissions/5fff37bf-d149-4d7e-a85c-f6e640092a4b

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
import Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_extension_identity_of_mem_compl
import Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_restr_apply

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
theorem _root_.solution (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) :
    restr (extId_mem hs hc hg) = g := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (restr_apply _ w).trans (extension_identity_of_mem_compl hc g w)
end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

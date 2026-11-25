-- Prove2me | solution 1 for Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.coe_mem_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:28.329555+00:00
-- url     : https://prove2.me/submissions/ad934294-ba8c-4019-bc44-f29651d75f06

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
import Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_mem_push

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
namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
theorem _root_.solution {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {x : ↥X} :
    (x : V) ∈ push X L ↔ x ∈ L := by
  rw [mem_push]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← Subtype.ext e]
  · intro hx
    exact ⟨x, hx, rfl⟩
end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

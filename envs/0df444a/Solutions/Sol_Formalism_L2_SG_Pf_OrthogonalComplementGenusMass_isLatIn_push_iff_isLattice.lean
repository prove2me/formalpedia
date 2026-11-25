-- Prove2me | solution 1 for Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.isLatIn_push_iff_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:48.815951+00:00
-- url     : https://prove2.me/submissions/a5772948-8998-40df-8adf-24e28459733c

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
import Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_incl_injective

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
theorem _root_.solution {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsLattice K L := by
  have hspan : Submodule.span K ((push X L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set ↥X)).map X.subtype := by
    rw [Submodule.map_span]
    congr 1
  constructor
  · rintro ⟨hfg, hsp⟩
    refine ⟨Submodule.fg_of_fg_map_injective _ (incl_injective X) hfg, ?_⟩
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [← hspan, hsp, Submodule.map_subtype_top]
  · rintro ⟨hfg, hsp⟩
    refine ⟨hfg.map _, ?_⟩
    rw [hspan, hsp, Submodule.map_subtype_top]
end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

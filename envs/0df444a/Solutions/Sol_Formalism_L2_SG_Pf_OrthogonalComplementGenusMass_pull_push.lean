-- Prove2me | solution 1 for Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.pull_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:34.409511+00:00
-- url     : https://prove2.me/submissions/56b15a1e-e1ca-467b-8f03-b770f8e412b7

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
theorem _root_.solution (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : pull X (push X L) = L :=
  Submodule.comap_map_eq_of_injective (incl_injective X) L
end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

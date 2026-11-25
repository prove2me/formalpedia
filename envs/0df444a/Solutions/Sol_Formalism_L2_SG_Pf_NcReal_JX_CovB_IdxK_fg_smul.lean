-- Prove2me | solution 1 for Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.fg_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:56.060058+00:00
-- url     : https://prove2.me/submissions/bf391e20-af68-41fa-8ef8-05e405d4817c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]
namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
theorem _root_.solution (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) (hN : N.FG) : (I • N).FG := by
  first
  | exact Submodule.FG.smul (IsNoetherian.noetherian I) hN
  | exact hN.smul (IsNoetherian.noetherian I)
  | (haveI : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hN
     have e : Submodule.map N.subtype (I • (⊤ : Submodule (𝓞 K) N)) = I • N := by
       rw [Submodule.map_smul'', Submodule.map_subtype_top]
     rw [← e]
     exact (IsNoetherian.noetherian _).map _)
end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK

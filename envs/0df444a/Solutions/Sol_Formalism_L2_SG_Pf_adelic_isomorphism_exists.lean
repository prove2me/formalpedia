-- Prove2me | solution 1 for Formalism.L2.SG.Pf.adelic_isomorphism_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:41:00.085629+00:00
-- url     : https://prove2.me/submissions/e40c1284-f113-42d5-be35-7402671eb8a9

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Theorems.Thm_Formalism_L2_SG_Pf_bridge_isBridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf
open NumberField IsDedekindDomain Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat Af IntAf)
variable (I : Formalism.MainNotions.S.AutInst)
variable (I : Formalism.MainNotions.S.AutInst)
namespace Formalism.L2.SG.Pf
theorem _root_.solution : AdBridgeIso I := by
  unfold AdBridgeIso
  exact ⟨bridge I, bridge_isBridge I⟩
end Formalism.L2.SG.Pf

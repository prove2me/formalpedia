-- Prove2me | solution 1 for Formalism.L2.SG.Pf.adelic_isomorphism_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:35.996664+00:00
-- url     : https://prove2.me/submissions/47cded60-b0b3-498b-be34-4f062b1f2415

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Theorems.Thm_Formalism_L2_SG_Pf_adelic_isomorphism_exists

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
theorem _root_.solution (hGF : AdBridgeGF I) (hK : AdBridgeK I) : AdelicIsomorphism I := by
  unfold AdelicIsomorphism
  exact ⟨adelic_isomorphism_exists I, hGF, hK⟩
end Formalism.L2.SG.Pf

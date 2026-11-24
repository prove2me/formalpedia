-- Prove2me | solution 1 for Formalism.L2.SG.Pf.bridge_isBridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:51.8431+00:00
-- url     : https://prove2.me/submissions/784dd7a5-b388-4d37-a6ad-077d63ff6b61

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement

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
theorem _root_.solution : IsBridge I (bridge I) := by
  intro x
  have hx := Fm_FmEquiv_symm I x
  refine ⟨fun v => ?_, ?_⟩
  · conv_lhs => rw [← hx]
    exact FmInf_val I v _
  · conv_lhs => rw [← hx]
    exact FmF_val I _
end Formalism.L2.SG.Pf

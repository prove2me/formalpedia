-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_m_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:20.995032+00:00
-- url     : https://prove2.me/submissions/a54ebbfb-65d7-4d7b-8ac3-42604d77f519

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_lR
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_sg_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (s : ℕ) (c : C) : D.Wt (rho D.l) (D.m s c) := by
  refine HasWt.mono ?_ (D.wt_m s c)
  have h1 := D.sg_pos
  have h2 : 0 < qnum D.l ^ s := by
    unfold qnum
    have := D.lR
    positivity
  nlinarith [mul_pos h2 h1]
end Formalism.BaseCaseIdentities.Data

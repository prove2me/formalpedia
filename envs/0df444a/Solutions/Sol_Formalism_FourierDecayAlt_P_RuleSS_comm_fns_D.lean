-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.comm_fns_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:32.778384+00:00
-- url     : https://prove2.me/submissions/d2a53606-4627-4a0a-a2e8-393f56ba93e0

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_mem_cbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_comm_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {x : A} (hx : x ∈ L.fns) :
    Commute x L.Dr ∧ Commute x L.Dri ∧ Commute x L.Drb ∧ Commute x L.Drbi :=
  ⟨comm_ofFn fun m => fcomm L hx (mem_c L m), comm_ofFn fun m => fcomm L hx (mem_ci L m),
    comm_ofFn fun m => fcomm L hx (mem_cb L m), comm_ofFn fun m => fcomm L hx (mem_cbi L m)⟩
end Formalism.FourierDecayAlt.P.RuleSS

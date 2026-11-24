-- Prove2me | solution 1 for Formalism.L2.Host.EQ_le_cycQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:01.527359+00:00
-- url     : https://prove2.me/submissions/7d6aca8d-8c35-4d11-ad54-5d0f93c7c0b1

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Theorems.Thm_Formalism_L2_Host_cycQ_mono
import Theorems.Thm_Formalism_L2_Host_cycQplus_le
import Theorems.Thm_Formalism_L2_Host_sqQ_le_cycQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution (e : ℕ) {q d : ℕ} (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    EQ e q d ≤ cycQ (condN e q d) := by
  have := Fact.mk hq
  have := Fact.mk hd
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (sqQ_le_cycQ hq4).trans (cycQ_mono (q_dvd_condN e q d))
  · exact (sqQ_le_cycQ hd4).trans (cycQ_mono (d_dvd_condN e q d))
  · exact (cycQplus_le _).trans (cycQ_mono (two_pow_dvd_condN e q d))
end Formalism.L2.Host

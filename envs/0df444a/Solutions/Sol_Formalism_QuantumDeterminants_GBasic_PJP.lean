-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.PJP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:09.902539+00:00
-- url     : https://prove2.me/submissions/ed972ebb-4dfd-475e-b4fa-d8d4b39db86c

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_PJP_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.GBasic
namespace Formalism.QuantumDeterminants.GBasic
theorem _root_.solution (k r : ℕ) : (Pk k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pk k r = Hpk k r := by
  ext i j
  exact PJP_apply k r i j
end Formalism.QuantumDeterminants.GBasic

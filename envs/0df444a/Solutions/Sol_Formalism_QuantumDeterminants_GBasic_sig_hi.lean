-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.sig_hi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:20.896804+00:00
-- url     : https://prove2.me/submissions/47676d90-6b0f-451d-a39e-738a1288acbe

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_val

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : r + k < i.val) :
    (sig k r i).val = 2 * r + k - i.val := by
  rw [sig_val, if_pos (Or.inr h)]
end Formalism.QuantumDeterminants.GBasic

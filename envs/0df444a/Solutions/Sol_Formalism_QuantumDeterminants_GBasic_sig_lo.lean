-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.sig_lo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:17.719829+00:00
-- url     : https://prove2.me/submissions/42b8e88d-624b-4b4b-9293-bb718c08efc8

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
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) (h : i.val < r) :
    (sig k r i).val = 2 * r + k - i.val := by
  rw [sig_val, if_pos (Or.inl h)]
end Formalism.QuantumDeterminants.GBasic

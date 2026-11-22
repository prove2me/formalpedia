-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.sig_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:10.5968+00:00
-- url     : https://prove2.me/submissions/736f264c-4bd4-445f-baa9-ddb371011b1e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) : sig k r i = sig k r j ↔ i = j := by
  constructor
  · intro h
    have e := congrArg (sig k r) h
    rwa [sig_sig, sig_sig] at e
  · intro h
    rw [h]
end Formalism.QuantumDeterminants.GBasic

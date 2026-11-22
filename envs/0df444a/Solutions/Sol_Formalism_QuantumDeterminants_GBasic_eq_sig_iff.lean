-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.eq_sig_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:17.031011+00:00
-- url     : https://prove2.me/submissions/094dd561-ed5e-419c-936e-568113d2eb25

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
theorem _root_.solution (k r : ℕ) (i l : Fin (2 * r + k + 1)) : i = sig k r l ↔ l = sig k r i := by
  constructor <;> intro h <;> subst h <;> rw [sig_sig]
end Formalism.QuantumDeterminants.GBasic

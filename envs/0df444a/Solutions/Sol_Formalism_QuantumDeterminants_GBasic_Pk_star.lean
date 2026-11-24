-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.Pk_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:37.323874+00:00
-- url     : https://prove2.me/submissions/9484c1f6-313d-4666-ae6e-cede80affbd4

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic

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
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pk k r i j) = Pk k r i j := by
  simp only [Pk, c1, c2]
  split_ifs <;> simp
end Formalism.QuantumDeterminants.GBasic

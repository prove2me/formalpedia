-- Prove2me | solution 1 for Formalism.QuantumDeterminants.group_factorization_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:36.815853+00:00
-- url     : https://prove2.me/submissions/aa41cd0d-a5e2-4c94-afac-2877d315c5ff

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds

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
namespace Formalism.QuantumDeterminants
theorem _root_.solution : GFactor := by
  intro k r z z' g h
  have hne : Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) ≠ 0 :=
    (Complex.normSq_pos.mpr h).ne'
  simp only [Gf, GGf, zeta, Complex.normSq_div]
  field_simp
end Formalism.QuantumDeterminants

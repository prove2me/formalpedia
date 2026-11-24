-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_re_star_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:32.910414+00:00
-- url     : https://prove2.me/submissions/e7dab443-a95a-4fb0-9aa5-10d857c57e2c

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

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
theorem _root_.solution (w : ℂ) : (star w * w).re = Complex.normSq w := by
  have h1 : star w * w = (Complex.normSq w : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  rw [h1, Complex.ofReal_re]
end Formalism.QuantumDeterminants

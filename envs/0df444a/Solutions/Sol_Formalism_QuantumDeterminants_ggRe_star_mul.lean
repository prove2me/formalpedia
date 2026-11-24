-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggRe_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:44.252167+00:00
-- url     : https://prove2.me/submissions/e6695fa8-ef57-419d-85e1-7855ee1b83a2

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (x : ℂ) : (star x * x).re = ‖x‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  first
  | (simp [Complex.mul_re]; ring)
  | simp [Complex.mul_re]
  | (simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring)
end Formalism.QuantumDeterminants

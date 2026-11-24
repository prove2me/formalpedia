-- Prove2me | solution 1 for Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_eq_re_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:37.227585+00:00
-- url     : https://prove2.me/submissions/2999bb2d-f939-4f16-bb63-379ad880ecff

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal

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
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q
namespace Formalism.MainNotions.S.Gauge.Cd
theorem _root_.solution (Z : Matrix ι ι ℂ) : hs2 Z = (Matrix.trace (Z * Zᴴ)).re := by
  unfold hs2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
end Formalism.MainNotions.S.Gauge.Cd

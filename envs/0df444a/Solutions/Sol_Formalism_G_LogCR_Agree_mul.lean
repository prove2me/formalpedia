-- Prove2me | solution 1 for Formalism.G.LogCR.Agree.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:38.451984+00:00
-- url     : https://prove2.me/submissions/aebf7525-0dea-4602-87df-b15aeb982c21

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace Formalism.G.LogCR
namespace Agree
theorem _root_.solution {N : ℕ} {x x' y y' : MvPowerSeries σ R} (hx : Agree N x x')
    (hy : Agree N y y') : Agree N (x * y) (x' * y') := by
  classical
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = d := by simpa using hp
  have h1 : p.1 ≤ d := hp' ▸ le_self_add
  have h2 : p.2 ≤ d := hp' ▸ le_add_self
  rw [hx p.1 (lt_of_le_of_lt (Finsupp.degree_mono h1) hd),
    hy p.2 (lt_of_le_of_lt (Finsupp.degree_mono h2) hd)]
end Agree
end Formalism.G.LogCR

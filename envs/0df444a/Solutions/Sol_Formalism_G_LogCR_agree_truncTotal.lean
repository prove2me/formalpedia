-- Prove2me | solution 1 for Formalism.G.LogCR.agree_truncTotal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:33.205474+00:00
-- url     : https://prove2.me/submissions/a6ab245b-cac4-4545-a9e9-7c916166fb42

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
theorem _root_.solution [Finite σ] (N : ℕ) (f : MvPowerSeries σ R) :
    Agree N f (truncTotal N f : MvPowerSeries σ R) := by
  intro d hd
  rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]
end Formalism.G.LogCR

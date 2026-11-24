-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_add_unitMultiIndex_apply_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:40.669055+00:00
-- url     : https://prove2.me/submissions/e96c4685-05d8-48a6-af2d-38b89edc7015

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_unitMultiIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α : Fin h → ℕ) (i : Fin h) (x : R) :
    multiIndexDeriv D (α + unitMultiIndex i) x = multiIndexDeriv D α (D i x) := by
  rw [multiIndexDeriv_add D hD α (unitMultiIndex i) x, multiIndexDeriv_unitMultiIndex D i x]
end FunctorialResolution.EmbeddedResolution

-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.la_card_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:43.248119+00:00
-- url     : https://prove2.me/submissions/86a2d270-9ba0-4408-996f-84cd9000556a

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Module Polynomial
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
namespace Formalism.GaloisIrreducibility
theorem _root_.solution [IsAlgClosed K] [FiniteDimensional K V] (φ : Module.End K V) :
    (LinearMap.charpoly φ).roots.card = finrank K V := by
  rw [← LinearMap.charpoly_natDegree φ]
  exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))
end Formalism.GaloisIrreducibility

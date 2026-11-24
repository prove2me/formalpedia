-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.StandardSmoothLift.liftedSubmersivePresentation_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:47.813232+00:00
-- url     : https://prove2.me/submissions/cc0ee755-ec99-4cdb-b0d1-2f5eeba2320c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLiftRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.StandardSmoothLift
variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)
namespace FunctorialResolution.EmbeddedResolution.StandardSmoothLift
theorem _root_.solution :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : Nat.card Unit = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
  have h1 : Nat.card (Unit ⊕ ι) = Nat.card ι + 1 := by
    rw [Nat.card_sum, hu]
    omega
  have h2 : Nat.card (Unit ⊕ σ) = Nat.card σ + 1 := by
    rw [Nat.card_sum, hu]
    omega
  show Nat.card (Unit ⊕ ι) - Nat.card (Unit ⊕ σ) = Nat.card ι - Nat.card σ
  rw [h1, h2]
  omega
end FunctorialResolution.EmbeddedResolution.StandardSmoothLift

-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.herm_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:29.974594+00:00
-- url     : https://prove2.me/submissions/2c6b7855-e440-470f-8c95-3c4046b4e0da

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (x : U) : (σ (h x x)).im = 0 := by
  have h1 : σ (h x x) = star (σ (h x x)) := by rw [← hσ, herm]
  have h2 := congrArg Complex.im h1
  have hs : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
  rw [hs, Complex.conj_im] at h2
  linarith
end Formalism.HermitianLatticeCounting.P

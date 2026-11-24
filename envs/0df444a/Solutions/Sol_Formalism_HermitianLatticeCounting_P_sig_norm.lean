-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sig_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:36.096748+00:00
-- url     : https://prove2.me/submissions/0cf85ffa-94da-443f-a22c-8fdaecf92225

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
theorem _root_.solution (σ : K →+* ℂ) (hσ : ∀ x : K, σ (star x) = star (σ x)) (a b : K) :
    (σ (a * star a * b)).re = Complex.normSq (σ a) * (σ b).re := by
  rw [map_mul, map_mul, hσ]
  have hs : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
  rw [hs]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring
end Formalism.HermitianLatticeCounting.P

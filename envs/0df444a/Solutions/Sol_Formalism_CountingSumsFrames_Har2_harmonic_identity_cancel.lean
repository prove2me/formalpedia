-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harmonic_identity_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:47.984036+00:00
-- url     : https://prove2.me/submissions/62ed72be-29a8-4c2b-a0be-f1a9e88d19e2

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (x y t s φ e : K) (hx : x ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0) (hφ : φ ≠ 0) (h : y * t = x * s) :
    e / x * (φ⁻¹ * φ⁻¹) + (e * -1) / y * ((t * φ)⁻¹ * (t * φ)⁻¹) * (t * s) = 0 := by
  obtain rfl : s = y * t / x := by
    rw [eq_div_iff hx]
    linear_combination -h
  field_simp
  all_goals ring
end Formalism.CountingSumsFrames.Har2

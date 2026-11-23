-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctr_h_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:58.261797+00:00
-- url     : https://prove2.me/submissions/18f4900f-b07c-45df-a361-4e5544fc2ee7

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h

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
theorem _root_.solution {a b : ℕ} (l : ℕ) {g : PolXY K k} (hg : g ∈ PolAB K k a b) :
    ctrF K k (hXY K k ^ (l + 1) * g) = hXY K k ^ (l + 1) * ctrF K k g +
      (((l + 1) * (a + b + k + l) : ℕ) : K) • (hXY K k ^ l * g) := by
  induction l with
  | zero =>
    rw [zero_add, pow_one, ctr_h hg]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
    push_cast
    ring
  | succ l ih =>
    rw [pow_succ' (hXY K k) (l + 1), mul_assoc, ctr_h (h_pow_mul_mem (l + 1) hg), ih]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
    push_cast
    ring
end Formalism.CountingSumsFrames.Har2

-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:19.869795+00:00
-- url     : https://prove2.me/submissions/8ae39486-fe53-44df-b274-2dafc8993acc

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_zero
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_apply
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_partial

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
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k (harProj K k A B f) = 0 := by
  rw [harProj_apply, ctr_partial hk hf (min A B) le_rfl, ctrF_pow_zero (Nat.lt_add_one _) hf, mul_zero,
    smul_zero]
end Formalism.CountingSumsFrames.Har2

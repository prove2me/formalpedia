-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.har_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:48.580317+00:00
-- url     : https://prove2.me/submissions/256c4854-1eac-4383-8f01-bd4dd66f7e58

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_indep
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_decomp_exists

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
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B a b : ℕ} {u g : PolXY K k} (hu : u ∈ HarAB K k A B)
    (hg : g ∈ PolAB K k a b) (h : u = hXY K k * g) : u = 0 := by
  obtain ⟨w, hw, hgw⟩ := decomp_exists hk a b g hg
  have key := har_indep hk (min a b + 1 + 1) (fun j => if j = 0 then A else a - (j - 1))
    (fun j => if j = 0 then B else b - (j - 1)) (fun j => if j = 0 then u else -w (j - 1))
    (fun j => by
      by_cases hj : j = 0
      · simp [hj, hu]
      · simp only [hj, ↓reduceIte]
        exact Submodule.neg_mem _ (hw (j - 1)))
    (by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, pow_zero, one_mul, mul_neg,
        Finset.sum_neg_distrib]
      rw [neg_add_eq_zero, h, hgw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc, ← pow_succ'])
  simpa using key 0 (by omega)
end Formalism.CountingSumsFrames.Har2

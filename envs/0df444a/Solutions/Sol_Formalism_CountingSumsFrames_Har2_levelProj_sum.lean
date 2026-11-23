-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.levelProj_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:40.995308+00:00
-- url     : https://prove2.me/submissions/26bc1b3d-2c41-4cc8-93f9-7e7520f760a1

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_decomp_exists
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_level

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
    ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f := by
  obtain ⟨w, hw, hfw⟩ := decomp_exists hk A B f hf
  conv_rhs => rw [hfw]
  conv_lhs => rw [hfw]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ min A B := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ∑ j ∈ range (min A B + 1), levelProj K k A B j (hXY K k ^ i * w i)
      = ∑ j ∈ range (min A B + 1), if i = j then hXY K k ^ i * w i else 0 :=
        Finset.sum_congr rfl fun j hj =>
          levelProj_level hk hi' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (hw i)
    _ = hXY K k ^ i * w i := by rw [Finset.sum_ite_eq, if_pos hi]
end Formalism.CountingSumsFrames.Har2

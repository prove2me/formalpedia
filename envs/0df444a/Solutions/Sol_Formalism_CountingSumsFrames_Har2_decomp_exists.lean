-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.decomp_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:50.497551+00:00
-- url     : https://prove2.me/submissions/a4a3fe17-3125-46cf-a5da-f49210cfeb52

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_sub
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_left
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_of_right

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
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) : ∀ (A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ∃ w : ℕ → PolXY K k, (∀ j, w j ∈ HarAB K k (A - j) (B - j)) ∧
      f = ∑ j ∈ range (min A B + 1), hXY K k ^ j * w j := by
  intro A
  induction A with
  | zero =>
    intro B f hf
    refine ⟨fun j => if j = 0 then f else 0, fun j => ?_, ?_⟩
    · by_cases hj : j = 0
      · subst hj
        simpa using har_of_left hf
      · simp [hj]
    · simp
  | succ A ih =>
    intro B f hf
    rcases B with _ | B
    · refine ⟨fun j => if j = 0 then f else 0, fun j => ?_, ?_⟩
      · by_cases hj : j = 0
        · subst hj
          simpa using har_of_right hf
        · simp [hj]
      · simp
    · obtain ⟨g, hg, hfg⟩ := harProj_sub hf
      simp only [Nat.add_sub_cancel] at hg
      obtain ⟨v, hv, hgv⟩ := ih B g hg
      refine ⟨fun j => if j = 0 then harProj K k (A + 1) (B + 1) f else v (j - 1), fun j => ?_, ?_⟩
      · by_cases hj : j = 0
        · subst hj
          simpa using harProj_mem hk hf
        · simp only [hj, ↓reduceIte]
          have := hv (j - 1)
          rwa [show A - (j - 1) = A + 1 - j by omega, show B - (j - 1) = B + 1 - j by omega] at this
      · rw [min_add_add_right, Finset.sum_range_succ']
        simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, pow_zero, one_mul]
        have e : f = harProj K k (A + 1) (B + 1) f + hXY K k * g := by rw [← hfg]; abel
        conv_lhs => rw [e]
        rw [hgv, Finset.mul_sum, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, ← pow_succ']
end Formalism.CountingSumsFrames.Har2

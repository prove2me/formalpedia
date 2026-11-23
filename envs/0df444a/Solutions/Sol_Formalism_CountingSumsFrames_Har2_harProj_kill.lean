-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harProj_kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:53.978693+00:00
-- url     : https://prove2.me/submissions/0918de5b-363e-4d73-af12-e929b11cf92d

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_sub
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_har_inter

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
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {g : PolXY K k}
    (hg : g ∈ PolAB K k (A - 1) (B - 1)) : harProj K k A B (hXY K k * g) = 0 := by
  have hhg : hXY K k * g ∈ PolAB K k A B := by
    have := h_mul_mem hg
    rwa [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] at this
  obtain ⟨g', hg', he⟩ := harProj_sub hhg
  exact har_inter hk (harProj_mem hk hhg) (Submodule.sub_mem _ hg hg') (by rw [mul_sub, ← he]; abel)
end Formalism.CountingSumsFrames.Har2

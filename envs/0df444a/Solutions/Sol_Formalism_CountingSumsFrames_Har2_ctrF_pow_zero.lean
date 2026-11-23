-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctrF_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:33.975935+00:00
-- url     : https://prove2.me/submissions/c4f9030b-c3a3-4ab3-85f9-e0a2a2dd0df3

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_zero_left
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_zero_right
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_mem

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
theorem _root_.solution {A B : ℕ} {l : ℕ} (hl : min A B < l) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    (ctrF K k ^ l) f = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + (min A B + 1) := ⟨l - (min A B + 1), by omega⟩
  rw [pow_add, Module.End.mul_apply, pow_succ', Module.End.mul_apply]
  have hm := ctrF_pow_mem (min A B) hf
  rcases le_total A B with h | h
  · rw [min_eq_left h] at hm ⊢
    rw [Nat.sub_self] at hm
    rw [ctrF_zero_left hm, map_zero]
  · rw [min_eq_right h] at hm ⊢
    rw [Nat.sub_self] at hm
    rw [ctrF_zero_right hm, map_zero]
end Formalism.CountingSumsFrames.Har2

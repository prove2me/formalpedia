-- Prove2me | solution 1 for ClauseBound.Rec.factorsThrough_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:42.117885+00:00
-- url     : https://prove2.me/submissions/a1005fda-20e8-448d-8312-734a9a5323b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_Number

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
namespace ClauseBound.Rec
theorem _root_.solution {Z Z' ι : Type} (S : Finset ι) (F : Z → Z' → ℤ) (f : ι → Z → ℤ) (f' : ι → Z' → ℤ) (b : ℤ) (c : ℕ)
    (hF : ∀ z z', F z z' = ∑ i ∈ S, f i z * f' i z') (hc : #S ≤ 2 ^ c) (hb : 0 < b)
    (hf : ∀ i ∈ S, ∀ z, |f i z| < b) (hf' : ∀ i ∈ S, ∀ z, |f' i z| < b) : FactorsThrough F c b := by
  classical
  have hcard : Fintype.card S ≤ Fintype.card (Bits c) := by simpa using hc
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have key : ∀ (i : S) (hi : ∃ j : S, e j = e i), hi.choose = i := fun i hi => e.injective hi.choose_spec
  refine ⟨fun z θ => if hθ : ∃ i : S, e i = θ then f hθ.choose z else 0,
    fun z' θ => if hθ : ∃ i : S, e i = θ then f' hθ.choose z' else 0, fun z z' => ?_, fun z θ => ?_, fun z' θ => ?_⟩
  · rw [hF, ← sum_coe_sort S, ← sum_subset (subset_univ (univ.map e)), sum_map]
    · refine sum_congr rfl fun i _ => ?_
      have hi : ∃ j : S, e j = e i := ⟨i, rfl⟩
      simp only [dif_pos hi, key i hi]
    · intro θ _ hθ
      have hn : ¬ ∃ i : S, e i = θ := fun ⟨i, hi⟩ => hθ (mem_map.2 ⟨i, mem_univ _, hi⟩)
      simp only [dif_neg hn, zero_mul]
  · by_cases hθ : ∃ i : S, e i = θ
    · simp only [dif_pos hθ]
      exact hf _ hθ.choose.2 z
    · simpa only [dif_neg hθ, abs_zero] using hb
  · by_cases hθ : ∃ i : S, e i = θ
    · simp only [dif_pos hθ]
      exact hf' _ hθ.choose.2 z'
    · simpa only [dif_neg hθ, abs_zero] using hb
end ClauseBound.Rec

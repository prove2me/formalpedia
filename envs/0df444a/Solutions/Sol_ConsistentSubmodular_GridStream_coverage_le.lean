-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.coverage_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:17.742707+00:00
-- url     : https://prove2.me/submissions/abb002c5-b0d5-4456-8b87-52ef6a9a045f

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
import Theorems.Thm_ConsistentSubmodular_GridStream_card_cover_le

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

theorem rowsHeld_add_columnsHeld (k : ℕ) {N : ℕ} (S : Finset (Fin N)) :
    rowsHeld k S + columnsHeld k S = S.card := by
  have h := card_filter_add_card_filter_not (s := S) (fun e : Fin N => e.val < k)
  have hnot : S.filter (fun e => ¬ e.val < k) = S.filter (fun e => k ≤ e.val) := by
    ext e
    simp [not_lt]
  rw [hnot] at h
  exact h

end ConsistentSubmodular.GridStream

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ) (hcard : S.card ≤ k)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    coverageValue (gridStreamCover k m) S ≤
      (rowsHeld k S : ℝ) * k + ((k : ℝ) - rowsHeld k S) * (k + j) -
        rowsHeld k S * ((k : ℝ) - rowsHeld k S) := by
  have h := card_cover_le S j hj
  have hsum := rowsHeld_add_columnsHeld k S
  have hnk : rowsHeld k S ≤ k := by omega
  have hck : columnsHeld k S + rowsHeld k S ≤ k := by omega
  have hcR : ((columnsHeld k S : ℕ) : ℝ) + rowsHeld k S ≤ k := by exact_mod_cast hck
  have hR : coverageValue (gridStreamCover k m) S ≤
      (rowsHeld k S : ℝ) * k + (columnsHeld k S : ℝ) * ((k : ℝ) - rowsHeld k S) +
        (columnsHeld k S : ℝ) * j := by
    unfold coverageValue
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub hnk] at hc
    exact hc
  have hkn : (0 : ℝ) ≤ (k : ℝ) - rowsHeld k S := by linarith [Nat.cast_nonneg (α := ℝ) (columnsHeld k S)]
  have hc1 : (columnsHeld k S : ℝ) ≤ (k : ℝ) - rowsHeld k S := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hc1 hkn, mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg (α := ℝ) j)]

end

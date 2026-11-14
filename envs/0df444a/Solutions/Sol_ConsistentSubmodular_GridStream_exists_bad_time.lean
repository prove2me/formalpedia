-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.exists_bad_time
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:57.093843+00:00
-- url     : https://prove2.me/submissions/22714f34-b7ed-4bd5-bfef-a00ac0cf79d4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
import Theorems.Thm_ConsistentSubmodular_GridStream_rowsHeld_le_add_recourse
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le_rows
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_rows
import Theorems.Thm_ConsistentSubmodular_GridStream_card_stageColumns
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_stage
import Theorems.Thm_ConsistentSubmodular_GridStream_exists_crossing
import Theorems.Thm_ConsistentSubmodular_GridStream_rows_after_stage
import Theorems.Thm_ConsistentSubmodular_GridStream_theorem3_chain

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

theorem card_arrivedPrefix {n t : ℕ} (h : t ≤ n) : (arrivedPrefix n t).card = t := by
  have hmap : (arrivedPrefix n t).map Fin.valEmbedding = range t := by
    ext x
    simp only [arrivedPrefix, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, hmap, card_range]

theorem arrivedPrefix_mono {n a b : ℕ} (h : a ≤ b) : arrivedPrefix n a ⊆ arrivedPrefix n b := by
  intro e he
  simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at he ⊢
  omega

theorem coverage_mono {n u : ℕ} (cover : Fin n → Finset (Fin u)) {A B : Finset (Fin n)}
    (h : A ⊆ B) : coverageValue cover A ≤ coverageValue cover B := by
  unfold coverageValue
  exact_mod_cast card_le_card (biUnion_subset_biUnion_of_subset_left _ h)

theorem coverage_nonneg {n u : ℕ} (cover : Fin n → Finset (Fin u)) (A : Finset (Fin n)) :
    0 ≤ coverageValue cover A :=
  Nat.cast_nonneg _

/-- A column set present at time `t` is from a stage at most `(t - 1) / k`: the
set `b_{i,j}` sits at the position `j k + i - 1 < t`, and its stage index in the
cover is `(e - k) / k = j - 1`. -/
theorem stage_lt_of_arrived {k N t : ℕ} (hk : 0 < k) {S : Finset (Fin N)}
    (hS : S ⊆ arrivedPrefix N t) : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < (t - 1) / k := by
  intro e he hke
  have het : e.val < t := by
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    exact this
  have h1 : (e.val - k) / k + 1 = e.val / k := by
    rw [← Nat.add_div_right _ hk, Nat.sub_add_cancel hke]
  have h2 : e.val / k ≤ (t - 1) / k := Nat.div_le_div_right (by omega)
  omega

theorem stageColumns_subset {k m j t : ℕ} (ht : (j + 1) * k ≤ t) :
    stageColumns k m j ⊆ arrivedPrefix (k + m * k) t := by
  intro e he
  simp only [stageColumns, arrivedPrefix, mem_filter, mem_univ, true_and] at he ⊢
  omega

end ConsistentSubmodular.GridStream

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

section Lemma6

variable {k m C : ℕ} {S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))}

/-- Part 1 of Lemma 6: once the rows have arrived, the comparison with all rows
forces `n_k ≥ 3k/4`. -/
theorem rows_at_k (hk : 0 < k) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * k ≤ 4 * rowsHeld k (S ⟨k, by omega⟩) := by
  set t₀ : Fin (k + m * k + 1) := ⟨k, by omega⟩
  have hA := happrox t₀ (arrivedPrefix (k + m * k) k) subset_rfl
    (card_arrivedPrefix (by omega)).le
  have hrows := coverage_rows (k := k) (m := m)
  have hS0 := coverage_le_rows (S t₀) (hS.2.1 t₀).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (3 * (k : ℝ)) * k ≤ (4 * (rowsHeld k (S t₀) : ℝ)) * k := by nlinarith
  exact_mod_cast le_of_mul_le_mul_right h hkR

end Lemma6

end ConsistentSubmodular.GridStream

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m : ℕ} {ε : ℝ} (hk : 0 < k) (hm : k ≤ m)
    (hεk : 1 / (k : ℝ) ≤ ε) (S : Fin (k + m * k + 1) → Finset (Fin (k + m * k)))
    (hS : FeasibleTrajectory k ⌊ε * k⌋₊ S) :
    ∃ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val ∧ A.card ≤ k ∧
      0 < coverageValue (gridStreamCover k m) A ∧
      coverageValue (gridStreamCover k m) (S t) ≤
        (3 / 4 + 6 * ε) * coverageValue (gridStreamCover k m) A := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hεk1 : 1 ≤ ε * k := by
    have := (div_le_iff₀ hkR).mp hεk
    linarith
  have hε0 : 0 < ε := by nlinarith
  have hmk := Nat.mul_le_mul_right k hm
  set t₀ : Fin (k + m * k + 1) := ⟨k, by omega⟩
  have hrows_card : (arrivedPrefix (k + m * k) k).card ≤ k := (card_arrivedPrefix (by omega)).le
  have hrows_cov := coverage_rows (k := k) (m := m)
  have hrows_pos : 0 < coverageValue (gridStreamCover k m) (arrivedPrefix (k + m * k) k) := by
    nlinarith
  by_cases hε4 : 1 / 4 ≤ ε
  · -- The trivial bound: at time `k` the ratio is at most `1 ≤ 3/4 + 6ε`.
    refine ⟨t₀, arrivedPrefix (k + m * k) k, subset_rfl, hrows_card, hrows_pos, ?_⟩
    have hmono := coverage_mono (gridStreamCover k m) (hS.2.1 t₀).1
    nlinarith
  push Not at hε4
  -- Otherwise the trajectory may be assumed to maintain a `3/4`-approximation.
  by_contra hno
  push Not at hno
  have happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t) := by
    intro t A hA hAc
    rcases (coverage_nonneg (gridStreamCover k m) A).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact coverage_nonneg _ _
    · have := hno t A hA hAc hpos
      nlinarith
  have h1 := rows_at_k hk hS happrox
  have h2 := rows_after_stage hk hm hS happrox
  -- The number of rows held, as a sequence indexed by time.
  set b : ℕ → ℝ := fun t =>
    if ht : t < k + m * k + 1 then (rowsHeld k (S ⟨t, ht⟩) : ℝ) else 0 with hb
  have hbt (t : ℕ) (ht : t < k + m * k + 1) : b t = rowsHeld k (S ⟨t, ht⟩) := by
    simp only [hb, dif_pos ht]
  have hfloor : (⌊ε * k⌋₊ : ℝ) ≤ ε * k := Nat.floor_le (by positivity)
  have hnk : (3 * k : ℝ) ≤ 4 * (rowsHeld k (S t₀) : ℝ) := by exact_mod_cast h1
  obtain ⟨t, hkt, hte, hlo, hhi⟩ := exists_crossing b (h := (k : ℝ) / 2)
    (δ := (⌊ε * k⌋₊ : ℝ)) (s := k) (e := k + k * k) (by omega)
    (by
      rw [hbt k (by omega)]
      linarith)
    (by
      rw [hbt _ (by omega)]
      have : 3 * (rowsHeld k (S ⟨k + k * k, by omega⟩) : ℝ) ≤ k := by
        exact_mod_cast h2
      linarith)
    (by
      intro t _ ht
      have htN : t < k + m * k := by omega
      rw [hbt t (by omega), hbt (t + 1) (by omega)]
      have hrec := hS.2.2 ⟨t, htN⟩
      have hle := rowsHeld_le_add_recourse k (S (Fin.succ ⟨t, htN⟩)) (S (Fin.castSucc ⟨t, htN⟩))
      have hle' : (rowsHeld k (S (Fin.castSucc ⟨t, htN⟩)) : ℝ) ≤
          rowsHeld k (S (Fin.succ ⟨t, htN⟩)) + ⌊ε * k⌋₊ := by
        exact_mod_cast hle.trans (Nat.add_le_add_left hrec _)
      simpa [Fin.succ_mk, Fin.castSucc_mk] using hle')
  -- The crossing time `t > k`, since `n_k ≥ 3k/4 > k/2 + εk`.
  have hεk4 : ε * k < k / 4 := by nlinarith
  have htk : k < t := by
    by_contra hcon
    have htk' : t = k := by omega
    have hbk : b t = rowsHeld k (S t₀) := by
      rw [htk']
      exact hbt k (by omega)
    linarith
  set T : Fin (k + m * k + 1) := ⟨t, by omega⟩
  rw [hbt t (by omega)] at hlo hhi
  set x : ℝ := (rowsHeld k (S T) : ℝ) with hx
  -- The stage `j = (t - 1) / k ≥ 1` of the crossing time.
  set j := (t - 1) / k with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hk).mpr (by
    rw [Nat.succ_mul]
    omega))
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  -- The trajectory covers at most `n k + (k - n)(k + j) - n (k - n)` elements.
  have hcov := coverage_le (S T) j (hS.2.1 T).2 (stage_lt_of_arrived hk (hS.2.1 T).1)
  rw [← hx] at hcov
  -- The last complete stage `B_{j-1}`, or `A` if `j = 1`, covers `k (k + j - 1)`.
  obtain ⟨A, hA, hAc, hAv⟩ : ∃ A : Finset (Fin (k + m * k)),
      A ⊆ arrivedPrefix (k + m * k) T.val ∧ A.card ≤ k ∧
      (k : ℝ) * (k + j - 1) ≤ coverageValue (gridStreamCover k m) A := by
    rcases Nat.lt_or_ge 1 j with hj2 | hj2
    · refine ⟨stageColumns k m (j - 1), stageColumns_subset ?_,
        (card_stageColumns (by omega)).le, ?_⟩
      · have hjt : j * k ≤ t - 1 := Nat.div_mul_le_self (t - 1) k
        rw [Nat.sub_add_cancel hj1]
        show j * k ≤ t
        omega
      · have hstage := coverage_stage (k := k) (m := m) (j := j - 1) (by omega) (by omega)
        rw [Nat.cast_sub hj1] at hstage
        push_cast at hstage
        linarith [show (k : ℝ) * (k + j - 1) = k * k + k * (j - 1) by ring]
    · have hj1' : j = 1 := le_antisymm hj2 hj1
      refine ⟨arrivedPrefix (k + m * k) k, arrivedPrefix_mono hkt, hrows_card, ?_⟩
      rw [hj1']
      push_cast
      linarith [show (k : ℝ) * (k + 1 - 1) = k * k by ring]
  have hApos : 0 < coverageValue (gridStreamCover k m) A := by nlinarith
  have hbad := hno T A hA hAc hApos
  -- The chain of inequalities of Appendix B.1 at the crossing time.
  have hx0 : (k : ℝ) / 2 ≤ x := by linarith
  have hx1 : x ≤ (k : ℝ) / 2 + ε * k := by linarith
  have hchain := theorem3_chain hkR hx0 hx1 hjR hε0 hε4 hεk1
  have hAv' := mul_le_mul_of_nonneg_left hAv (by linarith : (0 : ℝ) ≤ 3 / 4 + 6 * ε)
  linarith

end

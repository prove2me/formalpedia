-- Prove2me | solution 1 for ClassicalSchur.not_erProperty_four
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:31:10.360988+00:00
-- url     : https://prove2.me/submissions/ff8f09f0-5857-4da1-bae3-77703fb7875c

-- Generated from lean/ClassicalSchur/Values.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 9 file-scoped / sub-threshold helper(s)
--   rename  : not_erProperty_four -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurValues
import Mathlib



namespace ClassicalSchur

/-- Each prefix of `W` of length `L` has sum at most `4L`. -/
theorem seqW_prefix_sum_le : ∀ L ≤ 15, (seqW.take L).sum ≤ 4 * L := by
  decide

/-- A cover of `Y` restricts to a cover of any subset of `Y`. -/
theorem CoveredBySumFree.mono {X Y : Set ℕ} {q : ℕ} (hXY : X ⊆ Y)
    (h : CoveredBySumFree Y q) : CoveredBySumFree X q := by
  obtain ⟨C, hC, hY⟩ := h
  exact ⟨C, hC, hXY.trans hY⟩

/-- A cover by `q ≥ 1` sumfree sets bounds the Schur degree by `q`. -/
theorem sdeg_le_of_coveredBySumFree {X : Set ℕ} {q : ℕ} (hq : 1 ≤ q)
    (h : CoveredBySumFree X q) : sdeg X ≤ q :=
  sInf_le ⟨q, ⟨hq, h⟩, rfl⟩

/-- ER Proposition 2.5: the block sums of a block of `A` are block sums
of `A`. -/
theorem blockSums_mono_of_infix {A B : List ℕ} (h : B <:+: A) :
    blockSums B ⊆ blockSums A := by
  rintro s ⟨B', hB', hne, rfl⟩
  exact ⟨B', hB'.trans h, hne, rfl⟩

theorem seqW_prefix_diff_mem :
    ∀ j ≤ 15, ∀ i < j, ∃ t, (seqW.take j).sum - (seqW.take i).sum ∈ classesW t := by
  decide

/-- Every block sum is a difference of two prefix sums (ER Proposition 2.7,
the other direction). -/
theorem exists_of_mem_blockSums {A : List ℕ} {s : ℕ} (hs : s ∈ blockSums A) :
    ∃ i j, i < j ∧ j ≤ A.length ∧ s = (A.take j).sum - (A.take i).sum := by
  obtain ⟨B, ⟨u, v, rfl⟩, hne, rfl⟩ := hs
  have hB : 0 < B.length := List.length_pos_iff.mpr hne
  refine ⟨u.length, u.length + B.length, by omega, by simp only [List.length_append]; omega, ?_⟩
  have h1 : (u ++ B ++ v).take (u.length + B.length) = u ++ B := by
    rw [show u.length + B.length = (u ++ B).length by simp, List.take_left]
  have h2 : (u ++ B ++ v).take u.length = u := by
    rw [List.append_assoc, List.take_left]
  rw [h1, h2, List.sum_append]
  omega

theorem classesW_sumFree : ∀ i, ∀ x ∈ classesW i, ∀ y ∈ classesW i, x + y ∉ classesW i := by
  decide

/-- Lemma 2 of the note: three sumfree sets cover `Ŵ`. -/
theorem coveredBySumFree_blockSums_seqW : CoveredBySumFree (blockSums seqW) 3 := by
  refine ⟨fun i => ↑(classesW i), fun i x hx y hy => classesW_sumFree i x hx y hy, ?_⟩
  intro s hs
  obtain ⟨i, j, hij, hj, rfl⟩ := exists_of_mem_blockSums hs
  obtain ⟨t, ht⟩ := seqW_prefix_diff_mem j (by simpa [seqW] using hj) i hij
  exact Set.mem_iUnion.2 ⟨t, ht⟩

/-- For a nonempty sequence, `μ(A) ≤ n` holds exactly when the sum is at
most `n` times the length. -/
theorem average_le_iff {A : List ℕ} (hA : 0 < A.length) (n : ℕ) :
    average A ≤ n ↔ A.sum ≤ n * A.length := by
  have hL : (0 : ℚ) < A.length := by exact_mod_cast hA
  rw [average, div_le_iff₀ hL]
  norm_cast

end ClassicalSchur

open ClassicalSchur in
theorem solution {L : ℕ} (h0 : 0 < L) (hL : L ≤ 15) : ¬ ERProperty 4 L := by
  intro hP
  set B := seqW.take L with hB
  have hBlen : B.length = L := by simp [hB, seqW]; omega
  have hBpos : ∀ b ∈ B, 0 < b := fun b hb => by
    have hb' := List.mem_of_mem_take hb
    simp [seqW] at hb'
    omega
  have havg : average B ≤ (4 : ℕ) := by
    rw [average_le_iff (by omega), hBlen]
    exact seqW_prefix_sum_le L hL
  have hcov : CoveredBySumFree (blockSums B) 3 :=
    coveredBySumFree_blockSums_seqW.mono
      (blockSums_mono_of_infix (List.take_prefix L seqW).isInfix)
  have h := (hP B hBlen hBpos havg).trans (sdeg_le_of_coveredBySumFree (by norm_num) hcov)
  norm_cast at h

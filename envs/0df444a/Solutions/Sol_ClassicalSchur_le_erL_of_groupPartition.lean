-- Prove2me | solution 1 for ClassicalSchur.le_erL_of_groupPartition
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:40:03.294413+00:00
-- url     : https://prove2.me/submissions/197b7c6d-da70-4c24-895b-3822cc101e67

-- Generated from lean/ClassicalSchur/Lift.lean
--   imports : 4 platform node(s), 3 definition bundle(s)
--   inlined : 10 file-scoped / sub-threshold helper(s)
--   rename  : le_erL_of_groupPartition -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Definitions.Def_ClassicalSchurRamsey
import Theorems.Thm_ClassicalSchur_coveredBySumFree_liftSeq
import Theorems.Thm_ClassicalSchur_le_sdeg_blockSums
import Theorems.Thm_ClassicalSchur_liftPrefix_strictMono
import Theorems.Thm_ClassicalSchur_liftSeq_take_sum
import Mathlib



namespace ClassicalSchur

/-- With `M = 3m₁ − 2` every prefix of `liftSeq` has average at most 3. -/
theorem liftPrefix_le_three_mul (m₁ L : ℕ) :
    liftPrefix m₁ (3 * m₁ - 2) L ≤ 3 * L := by
  unfold liftPrefix
  have hdm := Nat.mod_add_div L m₁
  have : (3 * m₁ - 2) * (L / m₁) ≤ 3 * (m₁ * (L / m₁)) :=
    calc (3 * m₁ - 2) * (L / m₁) ≤ (3 * m₁) * (L / m₁) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 3 * (m₁ * (L / m₁)) := by ring
  omega

/-- A cover of `Y` restricts to a cover of any subset of `Y`. -/
theorem CoveredBySumFree.mono {X Y : Set ℕ} {q : ℕ} (hXY : X ⊆ Y)
    (h : CoveredBySumFree Y q) : CoveredBySumFree X q := by
  obtain ⟨C, hC, hY⟩ := h
  exact ⟨C, hC, hXY.trans hY⟩

/-- A cover by `q ≥ 1` sumfree sets bounds the Schur degree by `q`. -/
theorem sdeg_le_of_coveredBySumFree {X : Set ℕ} {q : ℕ} (hq : 1 ≤ q)
    (h : CoveredBySumFree X q) : sdeg X ≤ q :=
  sInf_le ⟨q, ⟨hq, h⟩, rfl⟩

theorem liftSeq_pos {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    ∀ a ∈ liftSeq m₁ m₂ M, 0 < a := by
  intro a ha
  simp only [liftSeq, List.mem_map, List.mem_range] at ha
  obtain ⟨k, -, rfl⟩ := ha
  have := liftPrefix_strictMono hm₁ hM (show k < k + 1 by omega)
  omega

/-- ER Proposition 2.5: the block sums of a block of `A` are block sums
of `A`. -/
theorem blockSums_mono_of_infix {A B : List ℕ} (h : B <:+: A) :
    blockSums B ⊆ blockSums A := by
  rintro s ⟨B', hB', hne, rfl⟩
  exact ⟨B', hB'.trans h, hne, rfl⟩

@[simp] theorem liftSeq_length (m₁ m₂ M : ℕ) : (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 := by
  simp [liftSeq]

/-- For a nonempty sequence, `μ(A) ≤ n` holds exactly when the sum is at
most `n` times the length. -/
theorem average_le_iff {A : List ℕ} (hA : 0 < A.length) (n : ℕ) :
    average A ≤ n ↔ A.sum ≤ n * A.length := by
  have hL : (0 : ℚ) < A.length := by exact_mod_cast hA
  rw [average, div_le_iff₀ hL]
  norm_cast

/-- The property of ER Definition 5.1 holds at every length `L` with
`ramseyBound k ≤ L + 1`, whatever the average. -/
theorem erProperty_of_ramseyBound (k L : ℕ) (hL : ramseyBound k ≤ L + 1) :
    ERProperty (k + 1) L := by
  intro A hlen _ _
  exact le_sdeg_blockSums (by omega)

theorem two_le_ramseyBound (k : ℕ) : 2 ≤ ramseyBound k := by
  cases k <;> simp [ramseyBound]

/-- A lower bound for `L(n)` from a lower bound for every length with the
property. The set is nonempty by `erProperty_of_ramseyBound`. -/
theorem le_erL {n m : ℕ} (hn : 1 ≤ n) (h : ∀ L, 0 < L → ERProperty n L → m ≤ L) :
    m ≤ erL n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h2 := two_le_ramseyBound k
  have hne : {L | 0 < L ∧ ERProperty (k + 1) L}.Nonempty :=
    ⟨ramseyBound k - 1, by omega, erProperty_of_ramseyBound k _ (by omega)⟩
  exact le_csInf hne fun L hL => h L hL.1 hL.2

end ClassicalSchur

open ClassicalSchur in
theorem solution {n m₁ m₂ : ℕ} (hn : 3 ≤ n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (C : Fin (n - 1) → Set (ZMod m₁ × ZMod m₂)) (hC : ∀ i, GroupSumFree (C i))
    (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) : m₁ * m₂ ≤ erL n := by
  refine le_erL (by omega) fun L hL hP => ?_
  by_contra! hlt
  have hM' : m₁ ≤ 3 * m₁ - 2 := by omega
  set A := liftSeq m₁ m₂ (3 * m₁ - 2) with hA
  have hLA : L ≤ m₁ * m₂ - 1 := by omega
  set B := A.take L with hB
  have hBlen : B.length = L := by simp [hB, hA]; omega
  have hBpos : ∀ b ∈ B, 0 < b := fun b hb =>
    liftSeq_pos hm₁ hM' b (List.mem_of_mem_take hb)
  have havg : average B ≤ n := by
    rw [average_le_iff (by omega), hBlen, hB, hA, liftSeq_take_sum hm₁ hM' hLA]
    exact (liftPrefix_le_three_mul m₁ L).trans (Nat.mul_le_mul_right L (by omega))
  have hcovB : CoveredBySumFree (blockSums B) (n - 1) :=
    (coveredBySumFree_liftSeq hm₁ hm₂ le_rfl C hC hcov).mono
      (blockSums_mono_of_infix (List.take_prefix L A).isInfix)
  have h := (hP B hBlen hBpos havg).trans (sdeg_le_of_coveredBySumFree (by omega) hcovB)
  norm_cast at h
  omega

-- Prove2me | solution 1 for ExponomialAssortment.FPTAS.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:00:40.037893+00:00
-- url     : https://prove2.me/submissions/2fa9cf62-db47-4a7c-8f55-403dbabec23b

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

open scoped BigOperators
open ExponomialAssortment.FPTAS

noncomputable def inst1 : Instance 2 where
  outside := 1
  price i := if i = 0 then (65 / 64 : ℝ) else 0
  utility _ := 0

private lemma valid_inst1 : Valid inst1 := by
  refine ⟨?_, ?_, ?_, ⟨0, rfl⟩, ?_⟩
  · intro i
    fin_cases i
    · simp [inst1]; norm_num
    · simp [inst1]
  · simp [inst1]
  · intro i j _
    simp [inst1]
  · intro i
    simp [inst1]

private lemma pmax_inst1_le : pmax inst1 ≤ 65 / 64 := by
  unfold pmax
  refine Finset.sup'_le _ _ ?_
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
  fin_cases i
  · simp [inst1]
  · simp [inst1]; norm_num

private lemma prefixSet_zero_empty : prefixSet (Finset.univ : Finset (Fin 2)) 0 = ∅ := by
  ext j
  simp [prefixSet]

theorem solution :
    ¬ (∀ (n : ℕ) (I : Instance n) (_hI : Valid I) (C : ℕ)
      (_hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (_hη : 0 < η) (_hp : ∃ i, 0 < I.price i)
      (S : Finset (Fin n)) (_hS : Feasible I C S),
      ∃ a, AverageTrajectory I η S a ∧ ∀ i : Fin n,
        average I S i.val ≤ a i.val ∧
        a i.val ≤ (1 + theta n η) ^ i.val * average I S i.val) := by
  intro h
  have hC : 1 ≤ (2 : ℕ) ∧ (2 : ℕ) ≤ 2 := ⟨by decide, by decide⟩
  have hη : (0 : ℝ) < 1 / 2 := by norm_num
  have hp : ∃ i : Fin 2, 0 < inst1.price i := ⟨0, by simp [inst1]⟩
  have hS : Feasible inst1 2 Finset.univ := ⟨Finset.mem_univ _, by simp⟩
  rcases h 2 inst1 valid_inst1 2 hC (1 / 2) hη hp Finset.univ hS with ⟨a, ha, _⟩
  have h0 := ha.2 0 (by decide)
  simp only [Finset.mem_univ, ↓reduceIte, Fin.val_zero, zero_add, prefixSet_zero_empty,
    Finset.card_empty, Nat.cast_zero, zero_mul, div_one] at h0
  have hp0 : inst1.price 0 = 65 / 64 := rfl
  rw [hp0] at h0
  rcases h0 with ⟨hgrid, hge, _⟩
  rcases hgrid with ha1_zero | ⟨k, hk_eq, _, hk_le_pmax⟩
  · linarith
  · have hle : a 1 ≤ 65 / 64 := le_trans hk_le_pmax pmax_inst1_le
    have hbase : 1 + theta 2 (1 / 2 : ℝ) = 33 / 32 := by
      unfold theta
      norm_num
    rw [hbase] at hk_eq
    rcases le_or_gt k 0 with hk_nonpos | hk_pos
    · have hpow : (33 / 32 : ℝ) ^ k ≤ (33 / 32 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hk_nonpos
      simp only [zpow_zero] at hpow
      linarith
    · have hk1 : (1 : ℤ) ≤ k := hk_pos
      have hpow : (33 / 32 : ℝ) ^ (1 : ℤ) ≤ (33 / 32 : ℝ) ^ k :=
        zpow_le_zpow_right₀ (by norm_num) hk1
      simp only [zpow_one] at hpow
      linarith

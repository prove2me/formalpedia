-- Prove2me | solution 1 for GaussMixGated.ExactReal.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @ligracew
-- created : 2026-11-13T07:58:04.813432+00:00
-- url     : https://prove2.me/submissions/eda8d948-dc80-4e97-8615-e64c577ed7e5

import Definitions.Def_GaussMixGated_ExactReal_Schedule

open GaussMixGated.ExactReal

theorem solution (d : ℕ) (hd : 1 ≤ d) (ε δ Ccov : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hC : 1 ≤ Ccov) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hb0 : b 0 ≤ betaSched d ε δ Ccov)
    (hrec : ∀ j < Jsched d δ, b j ≤ 1 / 2 →
      b (j + 1) ≤ b j + (1 - b j) *
        (3 * betaSched d ε δ Ccov + Ccov * (2 * b j + betaSched d ε δ Ccov))) :
    ∀ j ≤ Jsched d δ,
      b j ≤ 3 * Astar Ccov ^ j * betaSched d ε δ Ccov ∧
      3 * Astar Ccov ^ j * betaSched d ε δ Ccov ≤ ε ^ 2 / 1000 ∧
      b j ≤ 1 / 2 := by
  set A := Astar Ccov with hA_def
  set J := Jsched d δ with hJ_def
  set β := betaSched d ε δ Ccov with hβ_def
  have hA_ge_3 : 3 ≤ A := by rw [hA_def]; unfold Astar; linarith
  have hA_pos : 0 < A := by linarith
  have hβ_nonneg : 0 ≤ β := by
    rw [hβ_def]; unfold betaSched; positivity
  have h_upper : ∀ j ≤ J, 3 * A ^ j * β ≤ ε ^ 2 / 1000 := by
    intro j hj
    rw [hβ_def]; unfold betaSched
    have hpow : 3 * A ^ j ≤ A ^ (J + 1) := by
      calc 3 * A ^ j ≤ A * A ^ j := by gcongr
        _ = A ^ j * A := mul_comm _ _
        _ = A ^ (j + 1) := (pow_succ A j).symm
        _ ≤ A ^ (J + 1) := pow_le_pow_right₀ (by linarith) (Nat.succ_le_succ hj)
    have h1 : 3 * A ^ j ≤ ((J : ℝ) + 1) * A ^ (J + 1) := by
      calc 3 * A ^ j ≤ 1 * A ^ (J + 1) := by linarith
        _ ≤ ((J : ℝ) + 1) * A ^ (J + 1) := by
            gcongr
            linarith [Nat.cast_nonneg (α := ℝ) J]
    have hdenom_pos : 0 < 1000 * ((J : ℝ) + 1) * A ^ (J + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hdenom_pos (by norm_num : (0 : ℝ) < 1000)]
    have hmul : (3 * A ^ j * ε ^ 2) * 1000 ≤ (((J : ℝ) + 1) * A ^ (J + 1) * ε ^ 2) * 1000 := by
      gcongr
    linarith
  have hε_half : ε ^ 2 / 1000 ≤ 1 / 2 := by nlinarith
  have h_strong : ∀ j ≤ J, b j ≤ (3 * A ^ j - 2) * β := by
    intro j
    induction j with
    | zero =>
      intro _
      have : (3 * A ^ 0 - 2) * β = β := by ring
      rw [this]
      exact hb0
    | succ j ih =>
      intro hj
      have hj_lt : j < J := Nat.lt_of_succ_le hj
      have ih_j : b j ≤ (3 * A ^ j - 2) * β := ih (Nat.le_of_lt hj_lt)
      have hbj_le_3Aj : b j ≤ 3 * A ^ j * β := by linarith
      have hup_j : 3 * A ^ j * β ≤ ε ^ 2 / 1000 := h_upper j (Nat.le_of_lt hj_lt)
      have hbj_half : b j ≤ 1 / 2 := by linarith
      have hstep := hrec j hj_lt hbj_half
      have hbj_nonneg : 0 ≤ b j := hb j
      have h1_minus_bj : 1 - b j ≤ 1 := by linarith
      have h_inner_nonneg : 0 ≤ 3 * β + Ccov * (2 * b j + β) := by positivity
      have hstep2 : b (j + 1) ≤ A * b j + (3 + Ccov) * β := by
        have hmul : (1 - b j) * (3 * β + Ccov * (2 * b j + β))
            ≤ 1 * (3 * β + Ccov * (2 * b j + β)) :=
          mul_le_mul_of_nonneg_right h1_minus_bj h_inner_nonneg
        calc b (j + 1) ≤ b j + 1 * (3 * β + Ccov * (2 * b j + β)) := by linarith
          _ = (1 + 2 * Ccov) * b j + (3 + Ccov) * β := by ring
          _ = A * b j + (3 + Ccov) * β := rfl
      have h3Ccov : 3 + Ccov ≤ 2 * A - 2 := by
        rw [hA_def]; unfold Astar; linarith
      calc b (j + 1)
          ≤ A * b j + (3 + Ccov) * β := hstep2
        _ ≤ A * ((3 * A ^ j - 2) * β) + (2 * A - 2) * β := by
            have h1 : A * b j ≤ A * ((3 * A ^ j - 2) * β) :=
              mul_le_mul_of_nonneg_left ih_j hA_pos.le
            have h2 : (3 + Ccov) * β ≤ (2 * A - 2) * β :=
              mul_le_mul_of_nonneg_right h3Ccov hβ_nonneg
            linarith
        _ = (3 * A ^ (j + 1) - 2) * β := by
            rw [pow_succ]
            ring
  intro j hj
  have h1 : b j ≤ (3 * A ^ j - 2) * β := h_strong j hj
  have h2 : b j ≤ 3 * A ^ j * β := by linarith
  have h3 : 3 * A ^ j * β ≤ ε ^ 2 / 1000 := h_upper j hj
  exact ⟨h2, h3, by linarith⟩

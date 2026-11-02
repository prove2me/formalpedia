-- Prove2me | solution 1 for DirectFidelity.State.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:35:56.278206+00:00
-- url     : https://prove2.me/submissions/2f715444-b2fb-4ea1-9f17-9660f552aedd

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_prob_normalized
import Theorems.Thm_DirectFidelity_State_eq_9
set_option autoImplicit false

open DirectFidelity.State

theorem solution (n : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) * (∑ i, (mVec ρ ε δ ks i : ℝ)) ≤
      1 + 1 / (ε ^ 2 * δ) + 2 * dim n / ε ^ 2 * Real.log (2 / δ) := by
  set ℓ := ell ε δ
  have h_pos_arg : 0 < 1 / (ε ^ 2 * δ) := by positivity
  have hℓ : 0 < ℓ := Nat.ceil_pos.mpr h_pos_arg
  have hℓ_ne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hℓ)
  have hprob : ∑ k : P n, prob ρ k = 1 := by
    have hp := DirectFidelity.State.prob_normalized n ρ hρ
    exact hp.1.trans hp.2
  set S : ℝ := ∑ k : P n, prob ρ k * (mDFE ρ ε δ ℓ k : ℝ)
  have hj_eval : ∀ j : Fin ℓ,
      (∑ ks : Fin ℓ → P n, (∏ i, prob ρ (ks i)) * (mDFE ρ ε δ ℓ (ks j) : ℝ)) = S := by
    intro j
    have h1 : ∀ ks : Fin ℓ → P n,
        (∏ i, prob ρ (ks i)) * (mDFE ρ ε δ ℓ (ks j) : ℝ) =
          ∏ i : Fin ℓ, (prob ρ (ks i) * if i = j then (mDFE ρ ε δ ℓ (ks i) : ℝ) else 1) := by
      intro ks
      rw [Finset.prod_mul_distrib]
      congr 1
      have hite : (∏ i : Fin ℓ, if i = j then (mDFE ρ ε δ ℓ (ks i) : ℝ) else 1) =
          if j ∈ (Finset.univ : Finset (Fin ℓ)) then (mDFE ρ ε δ ℓ (ks j) : ℝ) else 1 := by
        simp [eq_comm]
      simpa using hite.symm
    simp_rw [h1]
    rw [← Fintype.prod_sum (fun (i : Fin ℓ) (k : P n) =>
      prob ρ k * if i = j then (mDFE ρ ε δ ℓ k : ℝ) else 1)]
    have h2 : ∀ i : Fin ℓ,
        (∑ k : P n, prob ρ k * if i = j then (mDFE ρ ε δ ℓ k : ℝ) else 1) =
          if i = j then S else 1 := by
      intro i
      split_ifs with hij
      · rfl
      · simpa using hprob
    simp_rw [h2]
    simp [eq_comm]
  have hLHS : (∑ ks : Fin ℓ → P n, (∏ i, prob ρ (ks i)) * (∑ i, (mVec ρ ε δ ks i : ℝ))) =
      (ℓ : ℝ) * S := by
    simp_rw [mVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hj_eval]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hLHS]
  have h9 : S ≤ 1 + 2 * dim n / ((ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ) :=
    DirectFidelity.State.eq_9 n ℓ ρ hρ ε δ hε hδ hδ1 hℓ
  have hmul : (ℓ : ℝ) * S ≤ (ℓ : ℝ) * (1 + 2 * dim n / ((ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)) :=
    mul_le_mul_of_nonneg_left h9 (Nat.cast_nonneg ℓ)
  have h_expand : (ℓ : ℝ) * (1 + 2 * dim n / ((ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)) =
      (ℓ : ℝ) + 2 * dim n / ε ^ 2 * Real.log (2 / δ) := by
    calc
      (ℓ : ℝ) * (1 + 2 * dim n / ((ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ))
          = (ℓ : ℝ) + ((ℓ : ℝ) * (2 * dim n / ((ℓ : ℝ) * ε ^ 2))) * Real.log (2 / δ) := by ring
      _ = (ℓ : ℝ) + (2 * dim n / ε ^ 2) * Real.log (2 / δ) := by
          congr 2
          field_simp [hℓ_ne, ne_of_gt hε]
  have h_ceil : (ℓ : ℝ) ≤ 1 + 1 / (ε ^ 2 * δ) := by
    have hc : (ℓ : ℝ) ≤ 1 / (ε ^ 2 * δ) + 1 := (Nat.ceil_lt_add_one h_pos_arg.le).le
    linarith
  linarith

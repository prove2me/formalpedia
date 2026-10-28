-- Prove2me | solution 1 for DirectFidelity.State.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:33:00.107905+00:00
-- url     : https://prove2.me/submissions/eb91d4aa-f668-4e9d-bb60-0a61aaa317e3

import Mathlib
import Definitions.Def_DirectFidelity_State_Setting

open DirectFidelity.State


theorem solution (n ℓ : ℕ) (ρ : Matrix (Q n) (Q n) ℂ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hℓ : 0 < ℓ) (ks : Fin ℓ → P n) (hks : ∀ i, chi ρ (ks i) ≠ 0) :
    Chof ρ ks (mVec ρ ε δ ks) =
        ∑ i, 4 / ((ℓ : ℝ) ^ 2 * (mVec ρ ε δ ks i : ℝ) * dim n * chi ρ (ks i) ^ 2) ∧
      Chof ρ ks (mVec ρ ε δ ks) ≤ 2 * ε ^ 2 / Real.log (2 / δ) := by
  have hdim : 0 < dim n := by unfold dim; positivity
  have hL : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hx : ∀ i, 0 < 2 / (dim n * chi ρ (ks i) ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ) := by
    intro i
    have := hks i
    positivity
  have hmx : ∀ i, 2 / (dim n * chi ρ (ks i) ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)
      ≤ (mVec ρ ε δ ks i : ℝ) := fun i => Nat.le_ceil _
  have hm0 : ∀ i, (0 : ℝ) < mVec ρ ε δ ks i := fun i => lt_of_lt_of_le (hx i) (hmx i)
  have hsq := Real.sq_sqrt hdim.le
  have hsq0 : 0 < Real.sqrt (dim n) := Real.sqrt_pos.mpr hdim
  have hterm : ∀ i, ∑ _j : Fin (mVec ρ ε δ ks i), (2 * cHoef ρ ks (mVec ρ ε δ ks) i) ^ 2
      = 4 / ((ℓ : ℝ) ^ 2 * (mVec ρ ε δ ks i : ℝ) * dim n * chi ρ (ks i) ^ 2) := by
    intro i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold cHoef
    have h1 := hm0 i
    have h2 := hks i
    field_simp
    rw [hsq]
    ring
  have heq : Chof ρ ks (mVec ρ ε δ ks) =
      ∑ i, 4 / ((ℓ : ℝ) ^ 2 * (mVec ρ ε δ ks i : ℝ) * dim n * chi ρ (ks i) ^ 2) := by
    unfold Chof
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  refine ⟨heq, ?_⟩
  rw [heq]
  calc ∑ i, 4 / ((ℓ : ℝ) ^ 2 * (mVec ρ ε δ ks i : ℝ) * dim n * chi ρ (ks i) ^ 2)
      ≤ ∑ _i : Fin ℓ, 2 * ε ^ 2 / ((ℓ : ℝ) * Real.log (2 / δ)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h2 := hks i
        have hc2 : 0 < chi ρ (ks i) ^ 2 := by positivity
        have e : 2 * ε ^ 2 / ((ℓ : ℝ) * Real.log (2 / δ)) = 4 / ((ℓ : ℝ) ^ 2 *
            (2 / (dim n * chi ρ (ks i) ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)) * dim n * chi ρ (ks i) ^ 2) := by
          field_simp
          ring
        rw [e]
        apply div_le_div_of_nonneg_left (by norm_num) (by have := hx i; positivity)
        have := hmx i
        gcongr
    _ = 2 * ε ^ 2 / Real.log (2 / δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

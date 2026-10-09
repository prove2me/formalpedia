-- Prove2me | solution 1 for BookProof.ChapterE2.exists_angles_realize
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:30:42.645216+00:00
-- url     : https://prove2.me/submissions/6cee2d9d-eb06-4711-a895-299037d45345

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.exists_angles_realize
import Mathlib
import Definitions.Def_ChapterE2
import Theorems.Thm_BookProof_ChapterE2_remainder_succ
import Theorems.Thm_BookProof_ChapterE2_stick_eq
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ θ : ℕ → ℝ, ∀ i : Fin n, bornProb θ n i = p i := by

  rcases n with ( _ | n );
  · aesop;
  · -- Set the remaining mass `R j = 1 - ∑ k ∈ Finset.range j, q k`.
    set q : ℕ → ℝ := fun k => if h : k < n + 1 then p ⟨k, h⟩ else 0
    set R : ℕ → ℝ := fun j => 1 - ∑ k ∈ Finset.range j, q k;
    -- Set the target conditional `t j = if R j = 0 then 0 else q j / R j`, and the angle `θ j =
    -- Real.arccos (Real.sqrt (t j))`.
    obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → ℝ, ∀ j, Real.cos (θ j) ^ 2 = if R j = 0 then 0 else q j / R j := by
      have h_t_range : ∀ j,        0 ≤ (if R j = 0 then 0 else q j / R j) ∧ (if R j = 0 then 0 else
          q j / R j) ≤ 1 := by
        intro j
        have hR_nonneg : 0 ≤ R j := by
          refine sub_nonneg_of_le ?_;
          by_cases hj : j ≤ n + 1;
          · rw [ ← hsum ];
            refine le_trans ( Finset.sum_le_sum (g := ?_) fun i hi => ?_ ) ?_;
            focus (use fun i => if h : i < n + 1 then p ⟨ i, h ⟩ else 0);
            · aesop;
            · refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hj ) fun _
                _ _ => ?_ ) ?_;
              · grind;
              · simp [ Finset.sum_range, Fin.sum_univ_castSucc ];
          · rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : n + 1 ≤ j ) ];
            simp? +zetaDelta at *;
            simp_all only [Fin.sum_univ_castSucc, sum_range, Fin.eta, dite_eq_ite, Fin.val_castSucc,
                Fin.is_le', ↓reduceIte, Fin.val_last, le_refl, add_le_iff_nonpos_right];
            exact Finset.sum_nonpos fun x hx => by split_ifs <;> linarith [ Finset.mem_Ico.mp hx ] ;
        have hq_le_R : q j ≤ R j := by
          have hq_le_R : ∑ k ∈ Finset.range (j + 1), q k ≤ 1 := by
            have hq_le_R : ∑ k ∈ Finset.range (j + 1), q k ≤ ∑ k ∈ Finset.range (n + 1), q k := by
              by_cases hj : j < n + 1;
              · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono (
                  by linarith ) ) fun _ _ _ => by aesop;
              · rw [ Finset.sum_subset ( Finset.range_mono ( by linarith : n + 1 ≤ j + 1 ) ) fun x
                                                                hx₁ hx₂ => by aesop ];
            exact hq_le_R.trans ( by rw [ ← hsum ] ; rw [ Finset.sum_range ] ; exact
                                     Finset.sum_le_sum fun i _ => by aesop );
          simp_all [ Finset.sum_range_succ ];
          linarith
        have ht_range : 0 ≤ (if R j = 0 then 0 else q j / R j) ∧ (if R j = 0 then 0 else q j / R j)
            ≤ 1 := by
          split_ifs <;> norm_num [ * ];
          exact ⟨ div_nonneg ( by aesop ) hR_nonneg, div_le_one_of_le₀ hq_le_R hR_nonneg ⟩
        exact ht_range;
      exact ⟨ fun j => Real.arccos ( Real.sqrt ( if R j = 0 then 0 else q j / R j ) ), fun j =>
          by rw [ Real.cos_arccos ] <;> nlinarith [ h_t_range j, Real.mul_self_sqrt ( h_t_range j
              |>.1 ) ] ⟩;
    -- Main claim: `remainder θ j = R j` for all j, by induction.
    have h_remainder : ∀ j, remainder θ j = R j := by
      intro j;
      induction j with
      | zero => ?_
      | succ j ih => ?_
      · unfold remainder R; norm_num;
      · have h_remainder_succ : remainder θ (j + 1) = remainder θ j * (1 - if R j = 0 then 0 else q
          j / R j) := by
          rw [ ← hθ j, remainder_succ ];
          rw [ Real.sin_sq ];
        by_cases hj : R j = 0 <;> simp_all only [↓reduceIte, sub_zero, mul_one] ;
        · simp? +zetaDelta at *;
          by_cases hj' : j ≤ n <;> simp_all [ Finset.sum_range_succ ];
          · have h_sum_le_one : ∑ k ∈ Finset.range (j + 1),            (if h : k ≤ n then p ⟨k,
              by linarith⟩ else 0) ≤ 1 := by
              rw [ ← hsum ];
              rw [ Finset.sum_fin_eq_sum_range ];
              rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : j + 1 ≤ n + 1 ) ];
              exact le_add_of_le_of_nonneg ( Finset.sum_le_sum fun _ _ =>
                  by split_ifs <;> linarith ) ( Finset.sum_nonneg fun _ _ =>
                      by split_ifs <;> linarith [ hp ⟨ _, by linarith [ Finset.mem_Ico.mp ‹_› ] ⟩ ]
                                                             );
            simp_all [ Finset.sum_range_succ ];
            linarith [ hp ⟨ j, by linarith ⟩ ];
          · grind;
        · simp? +zetaDelta at *;
          rw [ Finset.sum_range_succ, mul_sub, mul_one, mul_div_cancel₀ _ hj ] ; ring;
    use θ; intro i; simp only [bornProb, Order.lt_add_one_iff, Order.add_one_le_iff, h_remainder] ;
    split_ifs <;> simp_all only [Fin.sum_univ_castSucc, not_lt];
    · rw [ stick_eq, h_remainder, hθ ];
      split_ifs <;> simp_all [ mul_div_cancel₀ ];
      · have h_contra : ∑ k ∈ Finset.range (i + 1), q k ≤ ∑ k ∈ Finset.range (n + 1), q k := by
          exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono (
              by linarith ) ) fun _ _ _ => by aesop;
        simp +zetaDelta at *;
        simp_all [ Finset.sum_range, Fin.sum_univ_castSucc ];
        grind;
      · grind;
    · simp? +zetaDelta at *;
      simp_all only [Fin.val_last, lt_self_iff_false, not_false_eq_true, not_lt,
          Fin.eq_last_of_not_lt];
      simp_all only [sum_range, Fin.is_le', ↓reduceDIte];
      linarith!

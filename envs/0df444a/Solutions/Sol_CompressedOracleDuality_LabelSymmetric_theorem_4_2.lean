-- Prove2me | solution 1 for CompressedOracleDuality.LabelSymmetric.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:39:47.420391+00:00
-- url     : https://prove2.me/submissions/84296eff-459b-4d41-925b-b8133e60d2db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_gram_facts
import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_label_symmetry_transfer
import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_lemma_4_4
import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_54
import Theorems.Thm_CompressedOracleDuality_LabelSymmetric_equation_55

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CODMain
open CompressedOracleDuality.LabelSymmetric

lemma W_nonempty {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) : 1 ≤ Fintype.card W := by
  by_contra h
  push Not at h
  have hW : IsEmpty W := Fintype.card_eq_zero_iff.1 (by omega)
  have : A.start = 0 := by ext p; exact isEmptyElim p.2
  have h1 := A.start_unit
  rw [this, norm_zero] at h1
  exact zero_ne_one h1

lemma progress_zero {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) : progressAt A 0 = 0 := by
  rw [progressAt, norm_eq_zero]
  ext ⟨z, D⟩
  simp only [projectDatabase, WithLp.ofLp_toLp, if_true, PiLp.zero_apply]
  by_cases h : CollisionFree D
  · simp [h]
  · have hD : D ≠ fun _ => none := by
      rintro rfl; apply h; intro x₁ x₂ y h1; simp at h1
    simp only [h, not_false_eq_true, if_true]
    simp only [compressedStateAt, Fin.induction_zero, act, WithLp.ofLp_toLp, Matrix.mulVec,
      dotProduct, tensorVec, ket]
    apply Finset.sum_eq_zero
    rintro ⟨z', D'⟩ _
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, PiLp.single_apply]
    by_cases h' : D = D'
    · subst h'; simp [hD]
    · simp [h']

end CODMain

end

open QAlgorithms CompressedOracleDuality.LabelSymmetric CODMain
open scoped BigOperators MatrixOrder ComplexOrder

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ (n S T : ℕ) (W : Type) [Fintype W] [DecidableEq W]
      (A : QueryAlg (Input n) (Label n) W T) (out : Memory n W → CollisionOutput n),
      6 ≤ n → 2 ^ n * 2 ^ n * Fintype.card W ≤ 2 ^ S →
      IsLabelSymmetric A → (2 : ℝ) / 3 ≤ collisionSuccess A out →
      c * (2 : ℝ) ^ n * (n : ℝ) ≤ (T : ℝ) ^ 2 * (S : ℝ) := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  intro n S T W _ _ A out hn hmem hsym hsucc
  -- space: 2n ≤ S
  have hW := W_nonempty A
  have hS2 : 2 * n ≤ S := by
    have h1 : 2 ^ (2 * n) ≤ 2 ^ S := by
      calc 2 ^ (2 * n) = 2 ^ n * 2 ^ n * 1 := by ring
        _ ≤ 2 ^ n * 2 ^ n * Fintype.card W := Nat.mul_le_mul_left _ hW
        _ ≤ 2 ^ S := hmem
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hSn : n ≤ S := by omega
  have hNpos : (0:ℝ) < (2:ℝ)^n := by positivity
  have hN64 : (64:ℝ) ≤ (2:ℝ)^n := by
    calc (64:ℝ) = 2^6 := by norm_num
      _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hSreal : (2 * n : ℝ) ≤ S := by exact_mod_cast hS2
  by_cases hT : (2:ℝ)^n < (T:ℝ)^2
  · -- many queries
    have : (2:ℝ)^n * n ≤ (T:ℝ)^2 * S := by
      calc (2:ℝ)^n * n ≤ (T:ℝ)^2 * n := by gcongr
        _ ≤ (T:ℝ)^2 * S := by gcongr
    nlinarith
  push Not at hT
  -- per-query increment
  set δ : ℝ := Real.sqrt (16 * (12 * S / n) / (2:ℝ)^n) with hδ
  have hstep : ∀ t : Fin T, progressAt A t.succ - progressAt A t.castSucc ≤ δ := by
    intro t
    have h54 := equation_54 A hn t
    have hgf := gram_facts A t.castSucc hn hmem
    have hsymG := (label_symmetry_transfer A).1.1 hsym t.castSucc
    have ht2 : (t.castSucc : Fin (T+1)).val ^ 2 ≤ 2 ^ n := by
      have : ((t : ℕ) : ℝ) ^ 2 ≤ (2:ℝ)^n := by
        have ht : ((t : ℕ) : ℝ) ≤ T := by exact_mod_cast t.isLt.le
        nlinarith [sq_nonneg ((t : ℕ) : ℝ)]
      simp only [Fin.val_castSucc]
      exact_mod_cast this
    have h44 := (lemma_4_4 (gramAt A t.castSucc) hn ht2 hgf.1 hgf.2.1 hgf.2.2.2.2 hsymG
      hgf.2.2.2.1).2 S hSn hgf.2.2.1
    have hlog : Real.logb 2 ((2:ℝ)^n) = n := by
      rw [Real.logb_pow]; simp
    rw [hlog] at h44
    have hC : capacity (gramAt A t.castSucc) ≤ 12 * S / n := h44.trans (min_le_right _ _)
    refine h54.1.trans (h54.2.trans ?_)
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hNpos.le
    linarith
  -- telescoping
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have htel : ∀ k (hk : k ≤ T), progressAt A ⟨k, by omega⟩ ≤ k * δ := by
    intro k hk
    induction k with
    | zero => simp [show (⟨0, by omega⟩ : Fin (T+1)) = 0 from rfl, progress_zero]
    | succ k ih =>
      have h1 := ih (by omega)
      have h2 := hstep ⟨k, by omega⟩
      have e1 : (⟨k, by omega⟩ : Fin T).succ = (⟨k + 1, by omega⟩ : Fin (T+1)) := rfl
      have e2 : (⟨k, by omega⟩ : Fin T).castSucc = (⟨k, by omega⟩ : Fin (T+1)) := rfl
      rw [e1, e2] at h2
      push_cast; linarith
  have hfin := htel T le_rfl
  have hlast : (⟨T, by omega⟩ : Fin (T+1)) = Fin.last T := rfl
  rw [hlast] at hfin
  -- success bound
  have h55 := equation_55 A out hn
  have hsq : Real.sqrt (2/3) ≤ progressAt A (Fin.last T) + Real.sqrt (2 / (2:ℝ)^n) := by
    have := le_trans hsucc h55
    have hnn : 0 ≤ progressAt A (Fin.last T) + Real.sqrt (2 / (2:ℝ)^n) := by
      have : 0 ≤ progressAt A (Fin.last T) := norm_nonneg _
      positivity
    calc Real.sqrt (2/3) ≤ Real.sqrt ((progressAt A (Fin.last T) + Real.sqrt (2 / (2:ℝ)^n)) ^ 2) :=
          Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq hnn
  have h23 : (0.81:ℝ) ≤ Real.sqrt (2/3) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2N : Real.sqrt (2 / (2:ℝ)^n) ≤ 0.18 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [div_le_iff₀ hNpos]; nlinarith
  have hTd : (0.63:ℝ) ≤ T * δ := by linarith
  have hTd2 : (0.39:ℝ) ≤ (T * δ) ^ 2 := by nlinarith
  have hδ2 : δ ^ 2 = 16 * (12 * S / n) / (2:ℝ)^n := by
    rw [hδ, Real.sq_sqrt]; positivity
  rw [mul_pow, hδ2] at hTd2
  have key : (0.39:ℝ) * (2:ℝ)^n * n ≤ 192 * ((T:ℝ)^2 * S) := by
    have e : (T:ℝ)^2 * (16 * (12 * S / n) / (2:ℝ)^n) = 192 * ((T:ℝ)^2 * S) / (n * (2:ℝ)^n) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)] at hTd2
    linarith
  nlinarith

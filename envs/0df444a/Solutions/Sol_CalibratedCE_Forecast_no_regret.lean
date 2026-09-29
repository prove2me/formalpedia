-- Prove2me | solution 1 for CalibratedCE.Forecast.no_regret
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:33:04.574359+00:00
-- url     : https://prove2.me/submissions/a665a5c3-6a14-458a-84ee-8e57f41cefe4

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_Regret

namespace CalibratedCE.Forecast

lemma aux_nr_sq (a d : ℝ) : (max 0 (a + d))^2 ≤ (max 0 a + d)^2 := by
  rcases le_or_gt (a + d) 0 with h | h
  · rw [max_eq_left h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rw [max_eq_right h.le]
    have h1 : a ≤ max 0 a := le_max_right _ _
    exact pow_le_pow_left₀ h.le (by linarith) 2

lemma aux_nr_Rg_succ {k : ℕ} (L w : ℕ → Fin k → ℝ) (t : ℕ) (i j : Fin k) :
    Rg L w (t+1) i j = max 0 (S L w t i j + w t i * (L t i - L t j)) := by
  simp [Rg, S, Finset.sum_range_succ]

lemma aux_nr_w_le {k : ℕ} (p : Fin k → ℝ) (hp : IsDist p) (i : Fin k) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun a _ => hp.1 a) (Finset.mem_univ i)

lemma aux_nr_step (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (t : ℕ) :
    ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (Rg L w t i j)^2 + k := by
  set R := Rg L w t with hR
  set d : Fin k → Fin k → ℝ := fun i j => w t i * (L t i - L t j) with hd
  have h1 : ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (R i j + d i j)^2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    rw [aux_nr_Rg_succ]
    exact aux_nr_sq _ _
  have h2 : ∑ i, ∑ j, (R i j + d i j)^2
      = ∑ i, ∑ j, (R i j)^2 + 2 * ∑ i, ∑ j, R i j * d i j + ∑ i, ∑ j, (d i j)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have h3 : ∑ i, ∑ j, R i j * d i j = 0 := by
    have e1 : ∀ i, ∑ j, R i j * d i j
        = L t i * (w t i * ∑ j, R i j) - ∑ j, w t i * R i j * L t j := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; simp only [hd]; ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j => w t i * R i j * L t j)]
    have e2 : ∀ i, L t i * (w t i * ∑ j, R i j) = ∑ j, w t j * R j i * L t i := by
      intro i
      rw [hR, hflow t i, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [e2]
    exact sub_self _
  have h4 : ∑ i, ∑ j, (d i j)^2 ≤ k := by
    have hb : ∀ i j, (d i j)^2 ≤ w t i := by
      intro i j
      have hw0 := (hw t).1 i
      have hw1 := aux_nr_w_le _ (hw t) i
      have := hL t i
      have := hL t j
      simp only [hd]
      rw [mul_pow]
      have e3 : (L t i - L t j)^2 ≤ 1 := by nlinarith
      have e4 : (w t i)^2 ≤ w t i := by nlinarith
      have e5 : 0 ≤ (L t i - L t j)^2 := sq_nonneg _
      nlinarith
    calc ∑ i, ∑ j, (d i j)^2 ≤ ∑ i : Fin k, ∑ _j : Fin k, w t i :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = k := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum, (hw t).2, mul_one]
  have hk : ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (R i j)^2 + k := by
    rw [h2, h3] at h1; linarith
  exact hk

lemma aux_nr_pot (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) :
    ∑ i, ∑ j, (Rg L w T i j)^2 ≤ k * T := by
  induction T with
  | zero => simp [Rg, S]
  | succ n ih =>
    have := aux_nr_step k L w hL hw hflow n
    push_cast
    linarith

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem solution (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) (i j : Fin k) :
    Rg L w T i j ≤ Real.sqrt (2 * k * T) := by
  have hpot := aux_nr_pot k L w hL hw hflow T
  have hsq : (Rg L w T i j)^2 ≤ ∑ i, ∑ j, (Rg L w T i j)^2 := by
    have a1 : (Rg L w T i j)^2 ≤ ∑ j, (Rg L w T i j)^2 :=
      Finset.single_le_sum (f := fun j => (Rg L w T i j)^2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have a2 : ∑ j, (Rg L w T i j)^2 ≤ ∑ i, ∑ j, (Rg L w T i j)^2 :=
      Finset.single_le_sum (f := fun i => ∑ j, (Rg L w T i j)^2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    linarith
  have hkT : (0:ℝ) ≤ k * T := by positivity
  have h2 : (Rg L w T i j)^2 ≤ 2 * k * T := by nlinarith
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h2)

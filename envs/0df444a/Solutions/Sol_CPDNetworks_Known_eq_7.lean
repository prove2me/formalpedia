-- Prove2me | solution 1 for CPDNetworks.Known.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:05:44.824664+00:00
-- url     : https://prove2.me/submissions/8b263ba2-9ba1-4c0c-bb95-4a7476cc5f99

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Known_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace Aux_CPDNetworks_Known_eq_7

lemma cardI (T a b : ℕ) (hb : b ≤ T) (P : Fin T → Prop) [DecidablePred P]
    (hP : ∀ s : Fin T, P s ↔ a ≤ (s : ℕ) ∧ (s : ℕ) < b) :
    (Finset.univ.filter P).card = b - a := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (Finset.univ.filter P).map Fin.valEmbedding = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hP s).1 hs
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, (hP _).2 ⟨h1, h2⟩, rfl⟩
  rw [this, Nat.card_Ico]

lemma sumite {T : ℕ} (S : Finset (Fin T)) (Q : Fin T → Prop) [DecidablePred Q] (b a : ℝ) :
    ∑ s ∈ S, (if Q s then b else a) =
      ((S.filter Q).card : ℝ) * b + ((S.filter (fun s => ¬ Q s)).card : ℝ) * a := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

end Aux_CPDNetworks_Known_eq_7

open Aux_CPDNetworks_Known_eq_7 in
open CPDNetworks.Known in
theorem solution {n T : ℕ} (τ : ℕ) (hτ1 : 1 ≤ τ) (hτT : τ < T)
    (Θa Θb Pm : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (y : CPDNetworks.Lower.Obs n T) (t : ℕ), 1 ≤ t → t < T →
      CPDNetworks.Lower.cusum y t = -(mu T τ t) • (Pm ⊙ (Θa - Θb)) + noise (CPDNetworks.Lower.altParam τ Θa Θb Pm) y t) ∧
    (∀ t : ℕ, 1 ≤ t → t < T → mu T τ t ≤ mu T τ τ) ∧
    mu T τ τ = Real.sqrt T * CPDNetworks.Lower.q ((τ : ℝ) / T) := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hτTr : (τ : ℝ) < T := by exact_mod_cast hτT
  have hmuτ : mu T τ τ = Real.sqrt (τ * ((T : ℝ) - τ) / T) := by
    unfold mu
    rw [if_neg (by omega), if_pos le_rfl, div_self (by linarith)]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro y t ht1 htT
    have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have htTr : (t : ℝ) < T := by exact_mod_cast htT
    ext i j
    simp only [CPDNetworks.Lower.cusum, noise, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.sum_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.hadamard_apply,
      smul_eq_mul, Finset.sum_sub_distrib, CPDNetworks.Lower.altParam]
    simp only [apply_ite (fun M : Matrix (Fin n) (Fin n) ℝ => M i j), Matrix.hadamard_apply]
    rw [sumite, sumite, Finset.filter_filter, Finset.filter_filter, Finset.filter_filter,
      Finset.filter_filter]
    unfold mu
    have hne : (T : ℝ) - t ≠ 0 := by linarith
    have htne : (t : ℝ) ≠ 0 := by linarith
    rcases le_or_gt t τ with h | h
    · rw [cardI T 0 t htT.le (fun a : Fin T => (a : ℕ) < t ∧ (a : ℕ) < τ) (fun s => by omega),
        cardI T τ t htT.le (fun a : Fin T => (a : ℕ) < t ∧ ¬ (a : ℕ) < τ) (fun s => by omega),
        cardI T t τ hτT.le (fun a : Fin T => t ≤ (a : ℕ) ∧ (a : ℕ) < τ) (fun s => by omega),
        cardI T τ T le_rfl (fun a : Fin T => t ≤ (a : ℕ) ∧ ¬ (a : ℕ) < τ) (fun s => by omega),
        if_neg (by omega), if_pos h]
      rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h, Nat.cast_sub hτT.le, Nat.sub_zero]
      field_simp
      ring
    · rw [cardI T 0 τ hτT.le (fun a : Fin T => (a : ℕ) < t ∧ (a : ℕ) < τ) (fun s => by omega),
        cardI T τ t htT.le (fun a : Fin T => (a : ℕ) < t ∧ ¬ (a : ℕ) < τ) (fun s => by omega),
        cardI T t τ hτT.le (fun a : Fin T => t ≤ (a : ℕ) ∧ (a : ℕ) < τ) (fun s => by omega),
        cardI T t T le_rfl (fun a : Fin T => t ≤ (a : ℕ) ∧ ¬ (a : ℕ) < τ) (fun s => by omega),
        if_pos (by omega), if_neg (by omega)]
      rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_sub h.le, Nat.cast_sub htT.le, Nat.sub_zero]
      field_simp
      ring
  · intro t ht1 htT
    have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have htTr : (t : ℝ) < T := by exact_mod_cast htT
    rw [hmuτ]
    unfold mu
    rcases le_or_gt t τ with h | h
    · have hr : (t : ℝ) ≤ τ := by exact_mod_cast h
      rw [if_neg (by omega), if_pos h, zero_add]
      have hf : 0 ≤ ((T : ℝ) - τ) / ((T : ℝ) - t) := div_nonneg (by linarith) (by linarith)
      rw [← Real.sqrt_sq hf, ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) hT]
      have key : 0 ≤ (T : ℝ) * (T - t) * (T - τ) * (T * (τ - t)) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hT.le (by linarith : (0:ℝ) ≤ T - t))
          (by linarith : (0:ℝ) ≤ T - τ)) (mul_nonneg hT.le (by linarith : (0:ℝ) ≤ τ - t))
        exact this
      nlinarith [key]
    · have hr : (τ : ℝ) + 1 ≤ t := by exact_mod_cast h
      rw [if_pos (by omega), if_neg (by omega), add_zero]
      have hf : 0 ≤ (τ : ℝ) / t := by positivity
      rw [← Real.sqrt_sq hf, ← Real.sqrt_mul (div_nonneg (by nlinarith) hT.le)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) hT]
      have key : 0 ≤ (T : ℝ) * τ * t * (T * (t - τ)) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hT.le (by linarith : (0:ℝ) ≤ τ))
          (by linarith : (0:ℝ) ≤ t)) (mul_nonneg hT.le (by linarith : (0:ℝ) ≤ t - τ))
        exact this
      nlinarith [key]
  · rw [hmuτ, CPDNetworks.Lower.q, ← Real.sqrt_mul hT.le]
    congr 1
    field_simp

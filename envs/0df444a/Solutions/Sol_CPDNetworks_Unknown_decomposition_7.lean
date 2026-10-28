-- Prove2me | solution 1 for CPDNetworks.Unknown.decomposition_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:59:43.048664+00:00
-- url     : https://prove2.me/submissions/4212e283-ebef-4283-831e-af78e40f1d2f

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace Aux_CPD_d7

lemma cnt (T a b : ℕ) (p : Fin T → Prop) {inst : DecidablePred p}
    (hp : ∀ s : Fin T, p s ↔ a ≤ (s : ℕ) ∧ (s : ℕ) < b) (hb : b ≤ T) :
    (Finset.univ.filter p).card = b - a := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (Finset.univ.filter p).map Fin.valEmbedding = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact (hp s).mp hs
    · intro hx
      exact ⟨⟨x, by omega⟩, (hp _).mpr hx, rfl⟩
  rw [this, Nat.card_Ico]

lemma cnt2 (T a b : ℕ) (q r : Fin T → Prop) {i1 : DecidablePred q} {i2 : DecidablePred r}
    (hp : ∀ s : Fin T, (q s ∧ r s) ↔ a ≤ (s : ℕ) ∧ (s : ℕ) < b) (hab : a ≤ b) (hb : b ≤ T) :
    (((Finset.univ.filter q).filter r).card : ℝ) = (b : ℝ) - a := by
  rw [Finset.filter_filter, cnt T a b _ hp hb, Nat.cast_sub hab]

end Aux_CPD_d7

open CPDNetworks.Unknown Aux_CPD_d7 in
theorem solution (n T τ : ℕ) (Θa Θb Pi : Matrix (Fin n) (Fin n) ℝ)
    (hτ : 1 ≤ τ) (hτT : τ < T) :
    (∀ (y : CPDNetworks.Lower.Obs n T) (t : ℕ), 1 ≤ t → t < T →
      CPDNetworks.Lower.cusum y t = -(CPDNetworks.Known.mu T τ t) • (Pi ⊙ (Θa - Θb)) + CPDNetworks.Known.noise (CPDNetworks.Lower.altParam τ Θa Θb Pi) y t) ∧
    CPDNetworks.Known.mu T τ τ = Real.sqrt T * CPDNetworks.Lower.q ((τ : ℝ) / T) ∧
    (∀ t : ℕ, 1 ≤ t → t < T → CPDNetworks.Known.mu T τ t ≤ CPDNetworks.Known.mu T τ τ) := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hτr : (τ : ℝ) < T := by exact_mod_cast hτT
  have hτ1 : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hmuτ : CPDNetworks.Known.mu T τ τ = Real.sqrt (τ * ((T : ℝ) - τ) / T) := by
    unfold CPDNetworks.Known.mu
    rw [if_neg (by omega), if_pos le_rfl, zero_add, div_self (by linarith), mul_one]
  have hsum : ∀ S : Finset (Fin T), ∑ s ∈ S, CPDNetworks.Lower.altParam τ Θa Θb Pi s =
      (S.filter (fun s : Fin T => (s : ℕ) < τ)).card • (Pi ⊙ Θb) +
        (S.filter (fun s : Fin T => ¬ (s : ℕ) < τ)).card • (Pi ⊙ Θa) := by
    intro S
    unfold CPDNetworks.Lower.altParam
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  refine ⟨?_, ?_, ?_⟩
  · intro y t ht1 htT
    have htr : (t : ℝ) < T := by exact_mod_cast htT
    have ht1r : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    unfold CPDNetworks.Lower.cusum CPDNetworks.Known.noise
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum, hsum]
    rcases le_or_gt t τ with hle | hgt
    · have c1 := cnt2 T 0 t (fun s : Fin T => (s : ℕ) < t) (fun s : Fin T => (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) (by omega) (by omega)
      have c2 := cnt2 T t t (fun s : Fin T => (s : ℕ) < t) (fun s : Fin T => ¬ (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) le_rfl (by omega)
      have c3 := cnt2 T t τ (fun s : Fin T => t ≤ (s : ℕ)) (fun s : Fin T => (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) hle (by omega)
      have c4 := cnt2 T τ T (fun s : Fin T => t ≤ (s : ℕ)) (fun s : Fin T => ¬ (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) hτT.le le_rfl
      unfold CPDNetworks.Known.mu
      rw [if_neg (by omega), if_pos hle, zero_add]
      ext i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.hadamard_apply, smul_eq_mul]
      simp only [nsmul_eq_mul, c1, c2, c3, c4]
      have h1 : (T : ℝ) - t ≠ 0 := by linarith
      have h2 : (t : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    · have c1 := cnt2 T 0 τ (fun s : Fin T => (s : ℕ) < t) (fun s : Fin T => (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) (by omega) (by omega)
      have c2 := cnt2 T τ t (fun s : Fin T => (s : ℕ) < t) (fun s : Fin T => ¬ (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) hgt.le (by omega)
      have c3 := cnt2 T t t (fun s : Fin T => t ≤ (s : ℕ)) (fun s : Fin T => (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) le_rfl (by omega)
      have c4 := cnt2 T t T (fun s : Fin T => t ≤ (s : ℕ)) (fun s : Fin T => ¬ (s : ℕ) < τ) (i1 := inferInstance) (i2 := inferInstance)
        (fun s => by have := s.isLt; constructor <;> intro h <;> omega) htT.le le_rfl
      unfold CPDNetworks.Known.mu
      rw [if_pos (by omega), if_neg (by omega), add_zero]
      ext i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.hadamard_apply, smul_eq_mul]
      simp only [nsmul_eq_mul, c1, c2, c3, c4]
      have h1 : (T : ℝ) - t ≠ 0 := by linarith
      have h2 : (t : ℝ) ≠ 0 := by linarith
      field_simp
      ring
  · rw [hmuτ]
    unfold CPDNetworks.Lower.q
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    congr 1
    field_simp
  · intro t ht1 htT
    have htr : (t : ℝ) < T := by exact_mod_cast htT
    have ht1r : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    rw [hmuτ]
    unfold CPDNetworks.Known.mu
    have hx : 0 ≤ (t : ℝ) * ((T : ℝ) - t) / T := by
      apply div_nonneg _ hT.le; apply mul_nonneg <;> linarith
    rcases le_or_gt t τ with hle | hgt
    · have hler : (t : ℝ) ≤ τ := by exact_mod_cast hle
      rw [if_neg (by omega), if_pos hle, zero_add]
      have hc : 0 ≤ ((T : ℝ) - τ) / ((T : ℝ) - t) := by
        apply div_nonneg <;> linarith
      rw [← Real.sqrt_sq hc, ← Real.sqrt_mul hx]
      apply Real.sqrt_le_sqrt
      have e : (t : ℝ) * ((T : ℝ) - t) / T * (((T : ℝ) - τ) / ((T : ℝ) - t)) ^ 2 =
          t * ((T : ℝ) - τ) ^ 2 / (T * ((T : ℝ) - t)) := by
        have h1 : (T : ℝ) - t ≠ 0 := by linarith
        field_simp
      rw [e, div_le_div_iff₀ (by nlinarith) hT]
      have : (t : ℝ) * ((T : ℝ) - τ) ≤ τ * ((T : ℝ) - t) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by nlinarith : (0 : ℝ) ≤ ((T : ℝ) - τ) * T)]
    · have hgtr : (τ : ℝ) < t := by exact_mod_cast hgt
      rw [if_pos (by omega), if_neg (by omega), add_zero]
      have hc : 0 ≤ (τ : ℝ) / t := by positivity
      rw [← Real.sqrt_sq hc, ← Real.sqrt_mul hx]
      apply Real.sqrt_le_sqrt
      have e : (t : ℝ) * ((T : ℝ) - t) / T * ((τ : ℝ) / t) ^ 2 =
          ((T : ℝ) - t) * τ ^ 2 / (T * t) := by
        have h2 : (t : ℝ) ≠ 0 := by linarith
        field_simp
      rw [e, div_le_div_iff₀ (by nlinarith) hT]
      have : ((T : ℝ) - t) * τ ≤ ((T : ℝ) - τ) * t := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by nlinarith : (0 : ℝ) ≤ (τ : ℝ) * T)]

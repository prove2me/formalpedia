-- Prove2me | solution 1 for FreeOrderEPTAS.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:45:53.516963+00:00
-- url     : https://prove2.me/submissions/d453a87d-fa7f-44d0-afd1-2bc58017b780

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess

namespace Aux_FreeOrderEPTAS_lemma_2_2
open FreeOrderEPTAS

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by
  cases b <;> simp [bit]

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by
  cases b <;> simp [bit]

lemma sum_bit {n : ℕ} (s : Finset (Fin n)) (f : Fin n → Bool) :
    ∑ j ∈ s, bit (f j) = ((s.filter fun j => f j = true).card : ℝ) := by
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Bool.eq_false_or_eq_true (f j) with h | h <;> simp [bit, h]

end Aux_FreeOrderEPTAS_lemma_2_2

open Aux_FreeOrderEPTAS_lemma_2_2 in
open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ) (hϵ : 0 < ϵ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hδint : ∃ N : ℕ, 1 / δ = (N : ℝ)) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 2)
    (x : Assignment m n) (hcard : MeetsCard I x) (hload : LoadAtLeast I x 1)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo) :
    (mkLP I ϵ δ ξ Nlo Nhi Slo).Feasible (yhat I ϵ δ ξ x) := by
  -- coefficient bounds
  have hcoef : ∀ (i : Fin m) (t : Fin (numTypes I ϵ δ)),
      1 - ξ ≤ (if (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ then (1 : ℝ) else (1 - ξ)) ∧
      (if (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ then (1 : ℝ) else (1 - ξ)) ≤ 1 := by
    intro i t
    split_ifs <;> constructor <;> linarith
  -- sums over a type
  have hS3 : ∀ (i : Fin m) (t : Fin (numTypes I ϵ δ)),
      ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), yhat I ϵ δ ξ x i j =
        (if (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ then (1 : ℝ) else (1 - ξ)) *
          (Nip I ϵ δ x i t : ℝ) := by
    intro i t
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), yhat I ϵ δ ξ x i j =
        (if (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ then (1 : ℝ) else (1 - ξ)) *
          ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), bit (x i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      simp only [yhat, hj.2]
    rw [h1, sum_bit, Finset.filter_filter]
    first | done | rfl
  have hS4 : ∀ (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)),
      ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), I.ℓ i j d * yhat I ϵ δ ξ x i j =
        (if (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ then (1 : ℝ) else (1 - ξ)) *
          Sip I ϵ δ x i d t := by
    intro i d t
    unfold Sip
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_filter] at hj
    simp only [yhat, hj.2]
    ring
  have hSip0 : ∀ (i : Fin m) (d : Fin D) (t : Fin (numTypes I ϵ δ)), 0 ≤ Sip I ϵ δ x i d t := by
    intro i d t
    unfold Sip
    exact Finset.sum_nonneg fun j _ => mul_nonneg (I.ℓ_mem i j d).1 (bit_nonneg _)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- S1
    intro i j
    show yhat I ϵ δ ξ x i j ∈ Set.Icc (0 : ℝ) 1
    obtain ⟨hc1, hc2⟩ := hcoef i (rho I ϵ δ j)
    have hb0 := bit_nonneg (x i j)
    have hb1 := bit_le_one (x i j)
    refine ⟨?_, ?_⟩
    · exact mul_nonneg (by linarith) hb0
    · exact mul_le_one₀ hc2 hb0 hb1
  · -- S2
    intro j
    show ∑ i, yhat I ϵ δ ξ x i j ≤ 1
    calc ∑ i, yhat I ϵ δ ξ x i j ≤ ∑ i, bit (x i j) := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨hc1, hc2⟩ := hcoef i (rho I ϵ δ j)
          exact mul_le_of_le_one_left (bit_nonneg _) hc2
      _ = ((Finset.univ.filter fun i => x i j = true).card : ℝ) := sum_bit _ (fun i => x i j)
      _ ≤ 1 := by exact_mod_cast hcard.1 j
  · -- S3
    intro i t
    show (∑ j ∈ @Finset.filter _ (fun j => rho I ϵ δ j = t)
        (fun j => instDecidableEqFin _ (rho I ϵ δ j) t) Finset.univ, yhat I ϵ δ ξ x i j) ∈
      Set.Icc ((Nlo i t : ℕ) : ℝ) ((Nhi i t : ℕ) : ℝ)
    rw [hS3 i t]
    by_cases hN : (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ
    · rw [if_pos hN]
      obtain ⟨h1, h2⟩ := hg.exact i t hN
      rw [h1, h2, one_mul]
      exact ⟨le_rfl, le_rfl⟩
    · rw [if_neg hN]
      have hN' : 2 / δ < (Nip I ϵ δ x i t : ℝ) := lt_of_not_ge hN
      obtain ⟨h1, h2, h3⟩ := hg.approx i t hN'
      refine ⟨?_, h2⟩
      rw [h1]
      have hA : (1 / 2 : ℝ) * (Nip I ϵ δ x i t : ℝ) ≤ (1 - ξ) * (Nip I ϵ δ x i t : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      have hB : (1 / 2 : ℝ) * (2 / δ) = 1 / δ := by ring
      linarith
  · -- S4
    intro i d t hsmall
    have hs : d ∈ I.A i ∧ typeOf I ϵ δ t i d = 0 := by
      simpa [mkLP] using hsmall
    show (1 - ξ) * Slo i d t ≤
      ∑ j ∈ @Finset.filter _ (fun j => rho I ϵ δ j = t)
        (fun j => instDecidableEqFin _ (rho I ϵ δ j) t) Finset.univ, I.ℓ i j d * yhat I ϵ δ ξ x i j
    rw [hS4 i d t]
    obtain ⟨hc1, hc2⟩ := hcoef i t
    have hS0 := hSip0 i d t
    have hT : (0 : ℝ) < (numTypes I ϵ δ : ℝ) := by exact_mod_cast Fin.pos t
    have hq : 0 < ϵ / (numTypes I ϵ δ : ℝ) := div_pos hϵ hT
    have hSlo : Slo i d t ≤ Sip I ϵ δ x i d t := by
      rw [hg.small i d hs.1 t hs.2]
      have ha : 0 ≤ min (Sip I ϵ δ x i d t) 1 := le_min hS0 zero_le_one
      have hfl := Nat.floor_le (div_nonneg ha hq.le)
      have h2 := (le_div_iff₀ hq).mp hfl
      exact h2.trans (min_le_left _ _)
    have hxi : 0 ≤ 1 - ξ := by linarith
    calc (1 - ξ) * Slo i d t ≤ (1 - ξ) * Sip I ϵ δ x i d t :=
          mul_le_mul_of_nonneg_left hSlo hxi
      _ ≤ _ := mul_le_mul_of_nonneg_right hc1 hS0

-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.density_inert_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:55.00684+00:00
-- url     : https://prove2.me/submissions/c2db56b6-b4fe-4b4e-bd1d-bc7ad2346949

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_frob_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : InertDensity := by
  intro L _ _ _ q M β hcard hM hβ hβq
  classical
  obtain ⟨p, hchar⟩ := CharP.exists L
  obtain ⟨n, hp, hLn⟩ := FiniteField.card L p
  haveI := Fact.mk hp
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hLn, hcard, sq]⟩
  obtain ⟨k, -, hqk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hq2 : 2 ≤ q := by
    have h1 : 1 < q ^ 2 := hcard ▸ Fintype.one_lt_card
    by_contra h
    push_neg at h
    have : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have frob_sub : ∀ x y : L, (x - y) ^ q = x ^ q - y ^ q := by
    intro x y
    rw [hqk, sub_pow_char_pow]
  have hpow : ∀ x : L, x ^ (q ^ 2) = x := by
    intro x
    rw [← hcard]
    exact FiniteField.pow_card x

  have hNq : ∀ a : L, (a ^ (q + 1)) ^ q = a ^ (q + 1) := by
    intro a
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hpow, ← pow_succ']

  have hroots : ∀ (m : ℕ) (γ : L), 0 < m → (Finset.univ.filter (fun a : L => a ^ m = γ)).card ≤ m := by
    intro m γ hm
    calc (Finset.univ.filter (fun a : L => a ^ m = γ)).card
        ≤ (Polynomial.nthRoots m γ).toFinset.card := by
          apply Finset.card_le_card
          intro a ha
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm]
          exact (Finset.mem_filter.1 ha).2
      _ ≤ Multiset.card (Polynomial.nthRoots m γ) := Multiset.toFinset_card_le _
      _ ≤ m := Polynomial.card_nthRoots m γ
  set Fqs := Finset.univ.filter (fun b : L => b ^ q = b ∧ b ≠ 0) with hFqs
  have hmaps : ∀ a ∈ Finset.univ.erase (0 : L), a ^ (q + 1) ∈ Fqs := by
    intro a ha
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hNq a, pow_ne_zero _ (Finset.ne_of_mem_erase ha)⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard] at hsum
  have hle : ∀ γ ∈ Fqs,
      ((Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ)).card ≤ q + 1 := by
    intro γ _
    exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))
      (hroots (q + 1) γ (by omega))
  have hFqs : Fqs.card ≤ q - 1 := by
    refine le_trans (Finset.card_le_card ?_) (hroots (q - 1) 1 (by omega))
    intro b hb
    obtain ⟨-, hbq, hb0⟩ := Finset.mem_filter.1 hb
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, mul_right_cancel₀ hb0 ?_⟩
    rw [pow_sub_one_mul (by omega : q ≠ 0), one_mul, hbq]
  have hsq : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have heq : ∑ γ ∈ Fqs, ((Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ)).card =
      ∑ γ ∈ Fqs, (q + 1) := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [Finset.sum_const, smul_eq_mul, ← hsum, ← hsq]
    exact Nat.mul_le_mul_right _ hFqs
  have hfib := (Finset.sum_eq_sum_iff_of_le hle).1 heq

  have hc : ∀ γ : L, γ ^ q = γ →
      ((Finset.univ.filter (fun a : L => a ^ (q + 1) = γ)).card : ℝ) = if γ = 0 then 1 else q + 1 := by
    intro γ hγ
    split_ifs with h0
    · subst h0
      have : Finset.univ.filter (fun a : L => a ^ (q + 1) = 0) = {0} := by
        ext a
        simp [pow_eq_zero_iff (by omega : q + 1 ≠ 0)]
      rw [this, Finset.card_singleton, Nat.cast_one]
    · have hmem : γ ∈ Fqs := Finset.mem_filter.2 ⟨Finset.mem_univ _, hγ, h0⟩
      have e : (Finset.univ.erase (0 : L)).filter (fun a => a ^ (q + 1) = γ) =
          Finset.univ.filter (fun a : L => a ^ (q + 1) = γ) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨fun ha => h0 ?_, h⟩
          rw [← h, ha, zero_pow (by omega)]
      rw [← e, hfib γ hmem]

  have hrec : ∀ (m : ℕ) (γ : L),
      Fintype.card {x : Fin (m + 1) → L // ∑ i, x i ^ (q + 1) = γ} =
        ∑ a : L, Fintype.card {y : Fin m → L // ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1)} := by
    intro m γ
    rw [← Fintype.card_sigma]
    refine Fintype.card_congr (Equiv.trans ?_
      (Equiv.subtypeProdEquivSigmaSubtype (fun (a : L) (y : Fin m → L) =>
        ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1))))
    exact
      { toFun := fun x => ⟨(x.1 0, Fin.tail x.1), by
          have h := x.2
          rw [Fin.sum_univ_succ] at h
          show ∑ i : Fin m, x.1 i.succ ^ (q + 1) = γ - x.1 0 ^ (q + 1)
          linear_combination h⟩
        invFun := fun y => ⟨(Fin.cons y.1.1 y.1.2 : Fin (m + 1) → L), by
          rw [Fin.sum_univ_succ, Fin.cons_zero]
          simp only [Fin.cons_succ]
          linear_combination y.2⟩
        left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
        right_inv := fun y => Subtype.ext (by simp) }
  have hmain : ∀ (m : ℕ) (γ : L), γ ^ q = γ →
      (q : ℝ) * (Fintype.card {x : Fin m → L // ∑ i, x i ^ (q + 1) = γ} : ℝ) =
        if γ = 0 then (q : ℝ) ^ (2 * m) + (-1) ^ m * ((q : ℝ) - 1) * (q : ℝ) ^ m
        else (q : ℝ) ^ (2 * m) - (-1) ^ m * (q : ℝ) ^ m := by
    intro m
    induction m with
    | zero =>
      intro γ _
      split_ifs with h0
      · subst h0
        simp
      · have : Fintype.card {x : Fin 0 → L // ∑ i, x i ^ (q + 1) = γ} = 0 := by
          rw [Fintype.card_eq_zero_iff]
          exact ⟨fun ⟨x, hx⟩ => h0 (by simpa using hx.symm)⟩
        rw [this]
        simp
    | succ m ih =>
      intro γ hγ
      have hterm : ∀ a : L, (q : ℝ) *
          (Fintype.card {y : Fin m → L // ∑ i, y i ^ (q + 1) = γ - a ^ (q + 1)} : ℝ) =
          ((q : ℝ) ^ (2 * m) - (-1) ^ m * (q : ℝ) ^ m) +
            (q : ℝ) * (-1) ^ m * (q : ℝ) ^ m * (if a ^ (q + 1) = γ then 1 else 0) := by
        intro a
        rw [ih _ (by rw [frob_sub, hγ, hNq])]
        by_cases h : a ^ (q + 1) = γ
        · rw [if_pos (by rw [h, sub_self]), if_pos h]
          ring
        · rw [if_neg (fun h' => h (sub_eq_zero.1 h').symm), if_neg h]
          ring
      rw [hrec, Nat.cast_sum, Finset.mul_sum, Finset.sum_congr rfl (fun a _ => hterm a),
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
        ← Finset.mul_sum, Finset.sum_boole, hc γ hγ]
      push_cast
      split_ifs <;> ring
  have h := hmain M β hβq
  rw [if_neg hβ] at h
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [h2]
  have hS : (Fintype.card {x : Fin (j + 1) → L // ∑ i, x i ^ (q + 1) = β} : ℝ) =
      ((q : ℝ) ^ (2 * (j + 1)) - (-1) ^ (j + 1) * (q : ℝ) ^ (j + 1)) / q := by
    rw [← h]
    field_simp
  rw [hS]
  simp only [inv_pow]
  field_simp
  ring
end Formalism.HermitianLattices.GenusMassVolumes

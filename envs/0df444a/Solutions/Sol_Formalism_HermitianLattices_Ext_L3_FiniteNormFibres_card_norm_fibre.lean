-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:16.157798+00:00
-- url     : https://prove2.me/submissions/bb2df873-0a59-4e6c-b8e8-a12b4c388162

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteNormFibres_sigma_eq_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
namespace Formalism.HermitianLattices.Ext.L3.FiniteNormFibres
theorem _root_.solution {k : Type*} [Field k] [Fintype k] [DecidableEq k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (c : k) (hc : σ c = c) :
    ((univ.filter (fun y : k => σ y * y = c)).card : ℤ) =
      ((q : ℤ) - (-1)) + (-1) * (q : ℤ) * (if c = 0 then 1 else 0) := by
  have hpow := sigma_eq_pow σ hσ hne q hq
  have hne0 : ∀ y : k, y ≠ 0 → σ y ≠ 0 := fun y hy h => hy (σ.injective (by rw [h, map_zero]))
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Fintype.card k := Fintype.one_lt_card
    rw [hq] at h1
    by_contra h2
    have : q ≤ 1 := by omega
    have : q ^ 2 ≤ 1 := by nlinarith
    omega
  by_cases hc0 : c = 0
  · subst hc0
    have : univ.filter (fun y : k => σ y * y = 0) = {0} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hy
        exact mul_ne_zero (hne0 y hy) hy h
      · intro h
        rw [h, map_zero, zero_mul]
    rw [this, Finset.card_singleton, if_pos rfl]
    push_cast
    ring
  rw [if_neg hc0]

  set Fs := univ.filter (fun b : k => σ b = b ∧ b ≠ 0) with hFs
  set G : k → Finset k := fun b => univ.filter (fun y : k => σ y * y = b) with hG
  have hGle : ∀ b, (G b).card ≤ q + 1 := by
    intro b
    calc (G b).card ≤ (Polynomial.nthRoots (q + 1) b).toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega), pow_succ, ← hpow y, hy]
      _ ≤ (Polynomial.nthRoots (q + 1) b).card := Multiset.toFinset_card_le _
      _ ≤ q + 1 := Polynomial.card_nthRoots _ _
  have hFle : Fs.card ≤ q - 1 := by
    calc Fs.card ≤ (Polynomial.nthRoots (q - 1) (1 : k)).toFinset.card := by
          apply Finset.card_le_card
          intro b hb
          simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
          have h1 : b ^ (q - 1) * b = b := by
            rw [← pow_succ, show q - 1 + 1 = q by omega, ← hpow b, hb.1]
          have h2 : b ^ (q - 1) * b = 1 * b := by rw [h1, one_mul]
          exact mul_right_cancel₀ hb.2 h2
      _ ≤ (Polynomial.nthRoots (q - 1) (1 : k)).card := Multiset.toFinset_card_le _
      _ ≤ q - 1 := Polynomial.card_nthRoots _ _
  have hsum : ∑ b ∈ Fs, (G b).card = q ^ 2 - 1 := by
    have hmaps : ∀ y ∈ univ.filter (fun y : k => y ≠ 0), σ y * y ∈ Fs := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by rw [map_mul, hσ, mul_comm], mul_ne_zero (hne0 y hy) hy⟩
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    have h2 : (univ.filter (fun y : k => y ≠ 0)).card = q ^ 2 - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    congr 1
    ext y
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun hy => hb.2 ?_, h⟩
      rw [← h, hy, mul_zero]
    · exact fun h => h.2
  have hcF : c ∈ Fs := by
    simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hc0⟩
  have hGc : (G c).card = q + 1 := by
    by_contra hlt
    have hlt' : (G c).card < q + 1 := lt_of_le_of_ne (hGle c) hlt
    have h1 : ∑ b ∈ Fs, (G b).card < ∑ b ∈ Fs, (q + 1) :=
      Finset.sum_lt_sum (fun b _ => hGle b) ⟨c, hcF, hlt'⟩
    rw [Finset.sum_const, smul_eq_mul, hsum] at h1
    have h2 : Fs.card * (q + 1) ≤ (q - 1) * (q + 1) := Nat.mul_le_mul_right _ hFle
    have h3 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    omega
  have : (univ.filter (fun y : k => σ y * y = c)).card = q + 1 := hGc
  rw [this]
  push_cast
  ring
end Formalism.HermitianLattices.Ext.L3.FiniteNormFibres

-- Prove2me | solution 1 for DetANN.balanced_signs_exist
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T10:06:39.943207+00:00
-- url     : https://prove2.me/submissions/096d3279-1bfb-4a52-93b5-5fa26f3225ca

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_SignedBlocks
import Theorems.Thm_DetANN_expected_potential
import Theorems.Thm_DetANN_parseval_signed_blocks

open DetANN

theorem solution :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ P D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) →
            (∀ x ∈ P, ∀ y ∈ P, x ≠ y → x - y ∈ D ∨ y - x ∈ D) → 1 ≤ D.card →
            ∃ ξ : Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool,
              potential h (numReps C₀ τ (momentOrder D.card d)) ξ τ (momentOrder D.card d) D
                  ≤ 1 / 8 ∧
                (∀ v ∈ D, ∀ j : Fin d,
                  |(d : ℝ) * ‖signedBlocks h (numReps C₀ τ (momentOrder D.card d)) ξ j v‖ ^ 2
                      - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2) ∧
                IsBalancedBlockSystem τ P (signedBlocks h (numReps C₀ τ (momentOrder D.card d)) ξ)
                  := by
  obtain ⟨C, hC, C₀s, hC₀s, hEP⟩ := expected_potential
  refine ⟨C₀s, hC₀s, ?_⟩
  intro C₀ hC₀ d hd h hpm hh τ hτ0 hτ1 P D hD hdiff hN
  set p₀ := momentOrder D.card d with hp₀def
  set L := numReps C₀ τ p₀ with hLdef
  obtain ⟨e1, e2, e3⟩ := hEP C₀ hC₀ d hd h hpm τ hτ0 hτ1 D hD hN
  have havg : (Fintype.card (Fin L → Fin d → Bool) : ℝ)⁻¹ *
      ∑ ξ : Fin L → Fin d → Bool, potential h L ξ τ p₀ D ≤ 1 / 8 :=
    e1.trans (e2.trans e3)
  -- some sign assignment is at most the average
  have hcard : (0 : ℝ) < Fintype.card (Fin L → Fin d → Bool) := by exact_mod_cast Fintype.card_pos
  obtain ⟨ξ, -, hξ⟩ : ∃ ξ ∈ (Finset.univ : Finset (Fin L → Fin d → Bool)),
      potential h L ξ τ p₀ D ≤ 1 / 8 := by
    refine Finset.exists_le_of_sum_le Finset.univ_nonempty ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [inv_mul_le_iff₀ hcard] at havg
    exact havg
  -- p₀ ≥ 1 and L ≥ 1 (needed for Parseval)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (1 : ℝ) ≤ D.card := by exact_mod_cast hN
  have hp₀pos : 1 ≤ p₀ := by
    rw [hp₀def, momentOrder, Nat.one_le_ceil_iff]
    have : (1 : ℝ) ≤ D.card * d := one_le_mul_of_one_le_of_one_le hNR (by exact_mod_cast hd)
    exact Real.logb_pos (by norm_num) (by push_cast; nlinarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef, numReps, Nat.one_le_ceil_iff]
    have hp : (0 : ℝ) < p₀ := by exact_mod_cast hp₀pos
    exact mul_pos (mul_pos (lt_of_lt_of_le hC₀s hC₀) (by positivity)) hp
  -- every summand of Φ is at most Φ, hence < 1, which is the balance on 𝒟
  have hbalD : ∀ v ∈ D, ∀ j : Fin d,
      |(d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2 := by
    intro v hv j
    have hv0 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 (hD v hv); positivity
    have hnn : ∀ w ∈ D, ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ (((d : ℝ) * ‖signedBlocks h L ξ i w‖ ^ 2 - ‖w‖ ^ 2) / (τ * ‖w‖ ^ 2)) ^ (2 * p₀) :=
      fun w _ i _ => (even_two_mul p₀).pow_nonneg _
    have hterm : (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀)
        ≤ potential h L ξ τ p₀ D := by
      unfold potential
      calc _ ≤ ∑ i : Fin d,
            (((d : ℝ) * ‖signedBlocks h L ξ i v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) :=
            Finset.single_le_sum (hnn v hv) (Finset.mem_univ j)
        _ ≤ _ := Finset.single_le_sum (f := fun w => ∑ i : Fin d,
              (((d : ℝ) * ‖signedBlocks h L ξ i w‖ ^ 2 - ‖w‖ ^ 2) / (τ * ‖w‖ ^ 2)) ^ (2 * p₀))
            (fun w hw => Finset.sum_nonneg (hnn w hw)) hv
    set t := ((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)
    have ht : |t| < 1 := by
      by_contra hge
      push_neg at hge
      have : 1 ≤ t ^ (2 * p₀) := by
        rw [← (even_two_mul p₀).pow_abs]; exact one_le_pow₀ hge
      linarith
    have hpos : 0 < τ * ‖v‖ ^ 2 := mul_pos hτ0 hv0
    rw [abs_div, abs_of_pos hpos, div_lt_one hpos] at ht
    exact ht
  refine ⟨ξ, hξ, hbalD, ?_, ?_⟩
  · -- Parseval holds for every sign assignment
    intro z
    exact (parseval_signed_blocks h hh L hL1 ξ z).2
  · -- balance on all pairs of points of P
    intro x hx y hy i
    by_cases hxy : x = y
    · subst hxy; simp
    · have key : ∀ w ∈ D, (1 - τ) / d * ‖w‖ ^ 2 ≤ ‖signedBlocks h L ξ i w‖ ^ 2 ∧
          ‖signedBlocks h L ξ i w‖ ^ 2 ≤ (1 + τ) / d * ‖w‖ ^ 2 := by
        intro w hw
        have hb := hbalD w hw i
        rw [abs_lt] at hb
        constructor
        · rw [div_mul_eq_mul_div, div_le_iff₀ hdR]; linarith
        · rw [div_mul_eq_mul_div, le_div_iff₀ hdR]; linarith
      rcases hdiff x hx y hy hxy with hm | hm
      · exact key _ hm
      · have h1 : ‖signedBlocks h L ξ i (x - y)‖ = ‖signedBlocks h L ξ i (y - x)‖ := by
          rw [map_sub, map_sub, norm_sub_rev]
        have h2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
        rw [h1, h2]
        exact key _ hm

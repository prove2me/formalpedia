-- Prove2me | solution 1 for Finset.graph_balogSzemerediGowers_restricted_sumset
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:35:12.210027+00:00
-- url     : https://prove2.me/submissions/2d0a7ee9-d061-42cd-aac8-26b8428c0045

import Mathlib
import Theorems.Thm_Finset_dense_bipartite_has_path3_rectangle
import Theorems.Thm_Finset_path3_count_le_triple_rep_count
import Theorems.Thm_Finset_restricted_sumset_via_multiplicity

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ δ K : ℝ, 0 < δ → 0 < K → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A B : Finset G, A.Nonempty → B.Nonempty → A.card = B.card →
        ∀ E : Finset (G × G), E ⊆ A ×ˢ B →
          δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ) →
          ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ) →
          ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
            c * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            c * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
            ((A' + B').card : ℝ) ≤ C * (A.card : ℝ) := by
  -- ## High-level proof structure (length-3 path multiplicity argument).
  --
  -- Constants:
  -- * c := δ / 8 (from `dense_bipartite_has_path3_rectangle`, Fox-Sudakov DRC).
  -- * C := 2^13 K³ / δ^5 + 2^12 / δ^5, the path-multiplicity bound,
  --   absorbing both the M ≥ 1 and M = 0 sub-cases (triple-counting step in
  --   the proof of Tao-Vu Theorem 2.29, §6.4).
  intro δ K hδ hK
  refine ⟨δ / 8, 2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5,
    by positivity, by positivity, ?_⟩
  intro A B hA hB hAB E hE_sub hE_lb hS_ub
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  -- Compose the three sub-lemmas: `dense_bipartite_has_path3_rectangle` for
  -- the pointwise path-3 lower bound, `path3_count_le_triple_rep_count` for
  -- the path-to-triple-rep bridge, `restricted_sumset_via_multiplicity` for
  -- the cubic divisor. The Apop/Bpop scaffolding that previously prefixed
  -- this proof has been deleted; DRC supplies its own A', B' refinement.
  -- We must first handle the degenerate case `δ > 1`, which is vacuous
  -- since `δ · n² ≤ |E| ≤ n²`.
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1. Compose the three sub-lemmas.
    -- Restricted sumset image S.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    -- Convert hE_lb : δ · n² ≤ |E| to the rectangle form δ · |A| · |B| ≤ |E|.
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    -- Apply DRC pointwise path-3 rectangle.
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    -- Set the integer floor multiplicity M.
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    -- Pointwise lower bound on the triple-rep count via the path-3 bridge.
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    -- Apply restricted-sumset-via-multiplicity to obtain M · |A'+B'| ≤ |S|^3.
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    -- Bound |S|^3 ≤ K^3 · n^3.
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    -- Combine: M · |A' + B'| ≤ K^3 · n^3.
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    -- Refine to existential. The c · n bounds are exactly hA'_card, hB'_card
    -- since c = δ / 8 matches what DRC gave us; the |A' + B'| ≤ C · n bound
    -- requires case-splitting on M.
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      -- Two sub-cases: M = 0 or M ≥ 1.
      -- Constants we'll absorb into the final C = 2^13 K^3 / δ^5 + 2^12 / δ^5.
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h2pow12_pos : (0 : ℝ) < (2 : ℝ) ^ 12 := by positivity
      have h2pow13_pos : (0 : ℝ) < (2 : ℝ) ^ 13 := by positivity
      have hK3_pos : (0 : ℝ) < K ^ 3 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · -- M = 0 ⇒ (δ^5 / 2^12) · n² < 1 ⇒ n² < 2^12 / δ^5.
        have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        -- Crude bound: |A'+B'| ≤ |A'|·|B'| ≤ n·n = n².
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        -- Now 2^12/δ^5 ≤ (2^12/δ^5) · n since 1 ≤ n.
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        -- Combine: 2^12/δ^5 · n ≤ (2^13 K^3 / δ^5 + 2^12 / δ^5) · n.
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · -- M ≥ 1. Then M + 1 ≤ 2M, hence 2M > (δ^5/2^12)·n², so M > (δ^5/2^13)·n².
        have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have hM_pos_R : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM_geR
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge -- (δ^5/2^12)·n² - 1 < M
          linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        -- Multiply the lower bound on M by |A'+B'|:
        -- (δ^5/2^13)·n² · |A'+B'| ≤ M · |A'+B'| ≤ K^3 · n^3.
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        -- Divide by (δ^5/2^13)·n² > 0 to get |A'+B'| ≤ (2^13 K^3 / δ^5) · n.
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        -- Absorb into C.
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push Not at hδ_le  -- 1 < δ
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    -- So δ · n² ≤ n², hence δ ≤ 1 (since n² > 0), contradicting 1 < δ.
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith

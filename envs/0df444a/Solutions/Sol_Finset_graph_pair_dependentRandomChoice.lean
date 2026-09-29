-- Prove2me | solution 1 for Finset.graph_pair_dependentRandomChoice
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:43.310511+00:00
-- url     : https://prove2.me/submissions/1981f68a-78b0-411c-8b68-82bb22c7cd15

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (_hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by
  have hX_real_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hY_real_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hX_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hX_real_pos
  have hY_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hY_real_pos
  -- `U(v) := { x ∈ X : (x, v) ∈ F }`.
  set U : G → Finset G := fun v ↦ X.filter (fun x ↦ (x, v) ∈ F) with hU_def
  -- "Bad" ordered pairs in `X × X` (independent of `v`).
  set Bad : Finset (G × G) := (X ×ˢ X).filter fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
    (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBad_def
  -- The bad-in-U(v) finset is the restriction of `Bad` to `U(v) × U(v)`.
  set BadInV : G → Finset (G × G) := fun v ↦
    (U v ×ˢ U v).filter fun p : G × G ↦
      (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
        (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
      (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBadInV_def
  -- Step 1: Σ_v |U(v)| = |F|.
  have hSum_U_card : ∑ v ∈ Y, ((U v).card : ℝ) = (F.card : ℝ) := by
    have hF_filter : F = (X ×ˢ Y).filter (fun p : G × G ↦ p ∈ F) := by
      ext p
      refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · exact Finset.mem_filter.mpr ⟨hF_sub hp, hp⟩
      · exact (Finset.mem_filter.mp hp).2
    have hF_card_eq : (F.card : ℝ) = ∑ v ∈ Y, ((U v).card : ℝ) := by
      conv_lhs => rw [hF_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      push_cast
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [U, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    linarith
  -- Step 2: Σ_v |U(v)|² = Σ_{(x,x') ∈ X × X} codeg(x, x').
  set codeg : G × G → ℝ := fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) with hcodeg_def
  have hcodeg_nn : ∀ p, 0 ≤ codeg p := fun p ↦ Nat.cast_nonneg _
  have hSum_U_sq : ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 = ∑ p ∈ X ×ˢ X, codeg p := by
    have hStep : ∀ v ∈ Y,
        ((U v).card : ℝ) ^ 2 = ((U v ×ˢ U v).card : ℝ) := by
      intro v _
      rw [Finset.card_product]
      push_cast; ring
    rw [Finset.sum_congr rfl hStep]
    -- Σ_v |U(v) × U(v)| = Σ_v #{(x, x') ∈ X × X : (x, v) ∈ F ∧ (x', v) ∈ F}.
    have hStep2 : ∀ v ∈ Y, ((U v ×ˢ U v).card : ℝ) =
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ) := by
      intro v _
      have hSet : U v ×ˢ U v =
          (X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
        ext p
        simp only [Finset.mem_product, Finset.mem_filter, U]
        tauto
      rw [hSet]
    rw [Finset.sum_congr rfl hStep2]
    -- Swap sums: Σ_v #{(x,x'): (x,v)∈F ∧ (x',v)∈F} = Σ_{(x,x')} codeg(x,x').
    rw [show (∑ v ∈ Y,
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ)) =
        ∑ v ∈ Y, ∑ p ∈ X ×ˢ X,
          (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    -- codeg(p) = #{v ∈ Y : (p.1, v) ∈ F ∧ (p.2, v) ∈ F}.
    have hcodeg_eq : codeg p =
        ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
      simp only [codeg]
      rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
          = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
        ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    rw [hcodeg_eq]
  -- Step 3: Cauchy-Schwarz: |F|² ≤ |Y| · Σ_v |U(v)|².
  have hCS : (F.card : ℝ) ^ 2 ≤ (Y.card : ℝ) * ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ))
      (fun v ↦ ((U v).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_U_card] at h
    exact h
  -- Step 4: c²|X|²|Y| ≤ Σ_v |U(v)|².
  have hSum_U_sq_lb : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤
      ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hF_dense_nn : 0 ≤ c * (X.card : ℝ) * (Y.card : ℝ) :=
      mul_nonneg (mul_nonneg hc_nn hX_nn) hY_nn
    have hF_sq : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 ≤ (F.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hF_dense_nn hF_dense 2
    have hY_pos : 0 < (Y.card : ℝ) := hY_real_pos
    have h := le_trans hF_sq hCS
    have hrw : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 =
        (Y.card : ℝ) * (c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hY_pos
  -- Step 5: Σ_v |BadInV(v)| ≤ (ε c² / 2) |X|² |Y|.
  -- For each bad pair (x, x'), the number of v ∈ Y with x, x' ∈ U(v) equals
  -- codeg(x, x') ≤ (ε c² / 2)|Y|.
  have hSum_BadInV_le : ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
      (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
    -- Σ_v |BadInV(v)| = Σ_{p ∈ Bad} codeg(p).
    have hSwap : ∑ v ∈ Y, ((BadInV v).card : ℝ) = ∑ p ∈ Bad, codeg p := by
      -- Σ_v #{(x,x') ∈ U(v)² : p ∈ Bad}.
      have hStep : ∀ v ∈ Y, ((BadInV v).card : ℝ) =
          ∑ p ∈ Bad, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        intro v _
        -- BadInV(v) = Bad.filter (p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F).
        have hBadInV_eq : BadInV v =
            Bad.filter (fun p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
          ext p
          simp only [BadInV, Bad, Finset.mem_filter, Finset.mem_product, U,
            Finset.mem_filter]
          tauto
        rw [hBadInV_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [Finset.sum_congr rfl hStep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hcodeg_eq : codeg p =
          ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        simp only [codeg]
        rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
            = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
          ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [hcodeg_eq]
    rw [hSwap]
    -- Σ_{p ∈ Bad} codeg(p) ≤ |Bad| · (εc²/2)|Y| ≤ |X|² · (εc²/2)|Y|.
    have hBad_sub : Bad ⊆ X ×ˢ X := Finset.filter_subset _ _
    have hBad_card_le : (Bad.card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBad_sub
    have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
      rw [Finset.card_product]; push_cast; ring
    have hBad_card_le_X_sq : (Bad.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by
      rw [← hXX_card]; exact hBad_card_le
    have hτ_nn : 0 ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by positivity
    have hPointwise : ∀ p ∈ Bad, codeg p ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by
      intro p hp
      simp only [Bad, Finset.mem_filter] at hp
      exact le_of_lt hp.2
    calc ∑ p ∈ Bad, codeg p
        ≤ ∑ _p ∈ Bad, (ε * c ^ 2 / 2) * (Y.card : ℝ) :=
          Finset.sum_le_sum hPointwise
      _ = (Bad.card : ℝ) * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X.card : ℝ) ^ 2 * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hBad_card_le_X_sq hτ_nn
      _ = (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by ring
  -- Step 6: Σ_v Φ(v) ≥ (c² / 2) |X|² |Y|, where Φ(v) = |U(v)|² − (1/ε) |BadInV(v)|.
  set Φ : G → ℝ := fun v ↦
    ((U v).card : ℝ) ^ 2 - (1 / ε) * ((BadInV v).card : ℝ) with hΦ_def
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε_pos
  have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
  have hSum_Φ_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, Φ v := by
    have hSplit : ∑ v ∈ Y, Φ v =
        (∑ v ∈ Y, ((U v).card : ℝ) ^ 2) - (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) := by
      simp only [Φ]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSplit]
    have h1 : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 :=
      hSum_U_sq_lb
    have h2 : (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
        (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSum_BadInV_le hε_inv_nn
    have h2' : (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) =
        (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      field_simp
    rw [h2'] at h2
    linarith
  -- Step 7: Extract a `v` with Φ(v) ≥ (c²/2)|X|².
  have hSum_Φ_const : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) =
      ∑ _v ∈ Y, (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hSum_Φ_const] at hSum_Φ_lb
  obtain ⟨v, _hvY, hΦv⟩ := Finset.exists_le_of_sum_le hY hSum_Φ_lb
  -- Step 8: For this `v`, derive |U(v)| ≥ (c/2)|X| and |BadInV(v)| ≤ ε|U(v)|².
  -- From hΦv : (c²/2)|X|² ≤ |U(v)|² - (1/ε)|BadInV(v)|.
  -- Since |BadInV(v)| ≥ 0, |U(v)|² ≥ (c²/2)|X|² ≥ (c/2)²|X|² (because c ≤ 1).
  have hU_card_nn : (0 : ℝ) ≤ ((U v).card : ℝ) := Nat.cast_nonneg _
  have hBadInV_nn : (0 : ℝ) ≤ ((BadInV v).card : ℝ) := Nat.cast_nonneg _
  have hU_sq_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≥ 0 :=
      mul_nonneg hε_inv_nn hBadInV_nn
    linarith
  have hc_sq_half_ge_c_half_sq : (c / 2) ^ 2 ≤ c ^ 2 / 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have : (c / 2) ^ 2 = c ^ 2 / 4 := by ring
    rw [this]
    -- c²/4 ≤ c²/2 ↔ c² ≥ 0.
    nlinarith [sq_nonneg c]
  have hU_card_lb : (c / 2) * (X.card : ℝ) ≤ ((U v).card : ℝ) := by
    have hc_half_X_nn : (0 : ℝ) ≤ (c / 2) * (X.card : ℝ) :=
      mul_nonneg (by linarith) hX_nn
    have hsq_chain : ((c / 2) * (X.card : ℝ)) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
      calc ((c / 2) * (X.card : ℝ)) ^ 2
          = (c / 2) ^ 2 * (X.card : ℝ) ^ 2 := by ring
        _ ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq_half_ge_c_half_sq (sq_nonneg _)
        _ ≤ ((U v).card : ℝ) ^ 2 := hU_sq_lb
    have hsqrt := Real.sqrt_le_sqrt hsq_chain
    rwa [Real.sqrt_sq hc_half_X_nn, Real.sqrt_sq hU_card_nn] at hsqrt
  -- |BadInV(v)| ≤ ε |U(v)|².
  have hBadInV_le : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
    -- From hΦv: (c²/2)|X|² ≤ |U(v)|² − (1/ε)|BadInV(v)|.
    -- So (1/ε)|BadInV(v)| ≤ |U(v)|² − (c²/2)|X|² ≤ |U(v)|².
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≤ ((U v).card : ℝ) ^ 2 := by
      have hX_sq_nn : 0 ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε_pos)
      have heq : ε * ((1 / ε) * ((BadInV v).card : ℝ)) = ((BadInV v).card : ℝ) := by
        field_simp
      rw [heq] at this
      exact this
    exact h2
  -- Step 9: Package the witness.
  refine ⟨U v, ?_, hU_card_lb, ?_⟩
  · simp only [U]; exact Finset.filter_subset _ _
  · exact hBadInV_le

-- Prove2me | solution 1 for Finset.balog_szemeredi_gowers_asymmetric
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:37:16.039734+00:00
-- url     : https://prove2.me/submissions/f15e813c-60e7-442f-82f4-2db527735dfe

import Mathlib
import Theorems.Thm_Finset_graph_balogSzemerediGowers_restricted_sumset
import Theorems.Thm_Finset_popular_pairs_card_lower_bound
import Theorems.Thm_Finset_ruzsa_sumset_to_difference
import Theorems.Thm_Finset_sum_addConvolution_eq_card_product

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X Y : Finset G, X.Nonempty → Y.Nonempty → X.card = Y.card →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ) →
        ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
          ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) := by
  intro η hη
  -- Outer constants: graph_balogSzemerediGowers_restricted_sumset with (δ := η/2, K := 4/η), then
  -- Ruzsa adapter.
  obtain ⟨c₀, C₀, hc₀, hC₀, hGraphBSG⟩ :=
    graph_balogSzemerediGowers_restricted_sumset (G := G) (η / 2) (4 / η) (by linarith) (by positivity)
  -- Final constants
  refine ⟨min c₀ (η / 4), (C₀ / c₀) ^ 3 / c₀ + 1, ?_, ?_, ?_⟩
  · exact lt_min hc₀ (by linarith)
  · have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
    linarith
  intro X Y hX hY hXY hE
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  -- Case split on whether n is "large" or "small"
  by_cases hLarge : 2 ≤ (η / 2) * n
  · -- Substantive case: n ≥ 4/η, so floor((η/2)*n) ≥ 1 and ≥ (η/4)*n.
    set θ : ℕ := Nat.floor ((η / 2) * (n : ℝ)) with hθ_def
    have hηn_nn : 0 ≤ (η / 2) * (n : ℝ) := by positivity
    have hθ_floor_le : (θ : ℝ) ≤ (η / 2) * n := Nat.floor_le hηn_nn
    have hθ_floor_ge : (η / 2) * (n : ℝ) - 1 < θ := by
      have := Nat.lt_floor_add_one ((η / 2) * (n : ℝ))
      linarith
    have hθ_pos : 1 ≤ θ := by
      have : (1 : ℝ) ≤ θ := by linarith
      exact_mod_cast this
    have hθ_posR : (0 : ℝ) < θ := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hθ_pos)
    have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by
      have := hθ_floor_le
      linarith
    -- θ ≥ (η/4) * n
    have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
      have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
      have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
      linarith
    -- Define the popular bipartite graph E
    set E : Finset (G × G) :=
      (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) with hE_def
    have hE_sub : E ⊆ X ×ˢ Y := Finset.filter_subset _ _
    -- |E| ≥ (η/2) * n²
    have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hE_lb : (η / 2) * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have : (η / 2) * (n : ℝ) * Y.card = (η / 2) * (n : ℝ) ^ 2 := by
        rw [hYcard]; ring
      linarith
    -- S := image of E under (x,y) ↦ x + y
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    -- For each s ∈ S, X.addConvolution Y s ≥ θ.
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter] at hpE
      rw [← hps]; exact hpE.2
    -- S ⊆ X + Y.
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter, Finset.mem_product] at hpE
      rw [← hps]
      exact Finset.add_mem_add hpE.1.1 hpE.1.2
    -- |S| * θ ≤ ∑_{s ∈ S} addConv s ≤ ∑_{s ∈ X+Y} addConv s = n²
    have hSum_eq : ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card :=
      sum_addConvolution_eq_card_product X Y
    have hSum_S_le : (S.card : ℕ) * θ ≤ X.card * Y.card := by
      calc (S.card : ℕ) * θ
          = ∑ _s ∈ S, θ := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ s ∈ S, X.addConvolution Y s :=
            Finset.sum_le_sum hS_popular
        _ ≤ ∑ s ∈ X + Y, X.addConvolution Y s :=
            Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ ↦ Nat.zero_le _)
        _ = X.card * Y.card := hSum_eq
    -- Convert to reals: |S| * θ ≤ n²
    have hSum_S_le_R : (S.card : ℝ) * θ ≤ (n : ℝ) ^ 2 := by
      have h : ((S.card * θ : ℕ) : ℝ) ≤ ((X.card * Y.card : ℕ) : ℝ) := by
        exact_mod_cast hSum_S_le
      push_cast at h
      rw [hYcard] at h
      have hgoal : (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
      rw [hgoal]; exact h
    -- |S| ≤ n²/θ ≤ (4/η) * n
    have hS_le : (S.card : ℝ) ≤ (4 / η) * n := by
      have hS_le_nθ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
        rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
      have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
        rw [div_le_iff₀ hθ_posR]
        have hηpos : 0 < η := hη
        have h_θ_pos_q : (0 : ℝ) < (η / 4) * n := by positivity
        have h1 : (n : ℝ) ^ 2 = n * n := by ring
        rw [h1]
        have h_4η_pos : (0 : ℝ) < 4 / η := by positivity
        have hθ_ge' : (η / 4) * (n : ℝ) ≤ θ := hθ_ge_quarter
        -- (4/η * n) * θ ≥ (4/η * n) * (η/4 * n) = n * n
        have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by
          field_simp
        have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
          mul_le_mul_of_nonneg_left hθ_ge'
            (by positivity)
        linarith
      linarith
    -- Apply graph_balogSzemerediGowers_restricted_sumset
    have hδ : (η / 2) * (X.card : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      rw [← hn_def]; exact hE_lb
    have hK : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ (4 / η) * (X.card : ℝ) := by
      rw [← hn_def, ← hS_def]; exact hS_le
    obtain ⟨A', B', hA'sub, hB'sub, hA'lb, hB'lb, hAB'sumset⟩ :=
      hGraphBSG X Y hX hY hXY E hE_sub hδ hK
    -- Apply Ruzsa to get |A' - B'| ≤ (C₀/c₀)^3/c₀ * n
    have hA'pos : 0 < A'.card := by
      have : (0 : ℝ) < (A'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hA'ne : A'.Nonempty := Finset.card_pos.mp hA'pos
    have hB'pos : 0 < B'.card := by
      have : (0 : ℝ) < (B'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hB'ne : B'.Nonempty := Finset.card_pos.mp hB'pos
    -- Bound the sumset in terms of |A'|: |A' + B'| ≤ (C₀/c₀) * |A'|
    have hSumK : ((A' + B').card : ℝ) ≤ (C₀ / c₀) * A'.card := by
      have hC₀n_le : (C₀ : ℝ) * X.card ≤ (C₀ / c₀) * (c₀ * X.card) := by
        rw [show (C₀ / c₀) * (c₀ * (X.card : ℝ)) = C₀ * X.card by field_simp]
      have hcalc : (C₀ / c₀) * (c₀ * (X.card : ℝ)) ≤ (C₀ / c₀) * A'.card := by
        have hC₀c₀_pos : (0 : ℝ) < C₀ / c₀ := by positivity
        exact mul_le_mul_of_nonneg_left hA'lb (le_of_lt hC₀c₀_pos)
      linarith
    -- Balance: c₀ * |A'| ≤ |B'|, since |A'| ≤ |X| = n, so c₀ * |A'| ≤ c₀ * n ≤ |B'|.
    have hA'le_n : (A'.card : ℝ) ≤ n := by
      have : A'.card ≤ X.card := Finset.card_le_card hA'sub
      exact_mod_cast this
    have hBal : c₀ * (A'.card : ℝ) ≤ (B'.card : ℝ) := by
      have hc₀A'_le_c₀n : c₀ * (A'.card : ℝ) ≤ c₀ * X.card :=
        mul_le_mul_of_nonneg_left hA'le_n (le_of_lt hc₀)
      linarith
    obtain hRuzsa := ruzsa_sumset_to_difference (G := G)
      (C₀ / c₀) c₀ (by positivity) hc₀ A' B' hA'ne hB'ne hSumK hBal
    -- |A' - B'| ≤ (C₀/c₀)^3 / c₀ * |A'| ≤ (C₀/c₀)^3 / c₀ * n
    have hAmB'_le : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * n := by
      have h1 : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * A'.card := hRuzsa
      have hcoef_nn : (0 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) := by positivity
      have h2 : ((C₀ / c₀) ^ 3 / c₀) * A'.card ≤ ((C₀ / c₀) ^ 3 / c₀) * n :=
        mul_le_mul_of_nonneg_left hA'le_n hcoef_nn
      linarith
    refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ |A'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      calc min c₀ (η / 4) * (X.card : ℝ)
          ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (A'.card : ℝ) := hA'lb
    · -- min c₀ (η/4) * Y.card ≤ |B'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      calc min c₀ (η / 4) * (Y.card : ℝ)
          = min c₀ (η / 4) * X.card := by rw [hYn]
        _ ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (B'.card : ℝ) := hB'lb
    · -- |A' - B'| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hone_n_nn : (0 : ℝ) ≤ 1 * (X.card : ℝ) := by positivity
      have hexp : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          ((C₀ / c₀) ^ 3 / c₀) * X.card + (X.card : ℝ) := by ring
      rw [hexp]
      linarith
  · -- Small case: (η/2) * n < 2. Use singletons.
    push Not at hLarge
    obtain ⟨x, hxX⟩ := hX
    obtain ⟨y, hyY⟩ := hY
    refine ⟨{x}, {y}, Finset.singleton_subset_iff.mpr hxX,
        Finset.singleton_subset_iff.mpr hyY, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ 1
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({x} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- min c₀ (η/4) * Y.card ≤ 1
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      rw [hYn]
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({y} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- |{x} - {y}| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hsub_card : (({x} - {y} : Finset G)).card = 1 := by
        rw [Finset.singleton_sub_singleton]; simp
      have hcard1 : ((({x} - {y} : Finset G)).card : ℝ) = 1 := by
        rw [hsub_card]; simp
      rw [hcard1]
      have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
      have hone_le : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) * X.card := by
        have h1 : (1 : ℝ) ≤ (X.card : ℝ) := hn_ge_one
        have h2 : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) := by linarith
        nlinarith
      exact hone_le

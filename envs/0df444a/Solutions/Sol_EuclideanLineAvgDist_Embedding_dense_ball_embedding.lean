-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.dense_ball_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:12:15.819235+00:00
-- url     : https://prove2.me/submissions/9691b6f1-fb1c-4c3d-8f5b-bc61a0b49200

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic

section
open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist
open EuclideanLineAvgDist.Embedding

namespace Dev.DenseBall

theorem dtf_eq {X : Type*} [MetricSpace X] [Fintype X] (B : Finset X) (hB : B.Nonempty) (x : X) :
    distToFinset B x = B.inf' hB (fun y => dist x y) := by
  simp [distToFinset, hB]

theorem dtf_le_dist {X : Type*} [MetricSpace X] [Fintype X] (B : Finset X) (hB : B.Nonempty)
    (x b : X) (hb : b ∈ B) : distToFinset B x ≤ dist x b := by
  rw [dtf_eq B hB]; exact Finset.inf'_le _ hb

theorem dtf_nonneg {X : Type*} [MetricSpace X] [Fintype X] (B : Finset X) (hB : B.Nonempty)
    (x : X) : 0 ≤ distToFinset B x := by
  rw [dtf_eq B hB]; exact Finset.le_inf' _ _ (fun b _ => dist_nonneg)

theorem dtf_lipschitz {X : Type*} [MetricSpace X] [Fintype X] (B : Finset X) (hB : B.Nonempty)
    (x y : X) : distToFinset B x ≤ dist x y + distToFinset B y := by
  obtain ⟨b, hb, hfb⟩ := Finset.exists_mem_eq_inf' hB (fun b => dist y b)
  have h1 : distToFinset B y = dist y b := by rw [dtf_eq B hB]; exact hfb
  rw [h1]
  calc distToFinset B x ≤ dist x b := dtf_le_dist B hB x b hb
    _ ≤ dist x y + dist y b := dist_triangle _ _ _

theorem dtf_nonexp {X : Type*} [MetricSpace X] [Fintype X] (B : Finset X) (hB : B.Nonempty) :
    NonExpansive (distToFinset B) := by
  intro x y
  rw [abs_le]
  constructor
  · have := dtf_lipschitz B hB y x
    rw [dist_comm] at this; linarith
  · have := dtf_lipschitz B hB x y
    linarith

end Dev.DenseBall

open Dev.DenseBall in
theorem chk_dense_ball_embedding {X : Type*} [MetricSpace X] [Fintype X]
    (κ c : ℝ) (hκ : 0 < κ) (hc : 2 < c) (xstar : X)
    (hdense : κ * (Fintype.card X : ℝ) ≤ ((ball xstar (avgDist X / c)).card : ℝ)) :
    NonExpansive (distToFinset (ball xstar (avgDist X / c))) ∧
      distSum X ≤ (1 / ((κ / 2) * (1 - 2 / c))) *
        lineSpread (distToFinset (ball xstar (avgDist X / c))) := by
  classical
  set B := ball xstar (avgDist X / c) with hBdef
  have hn : (0 : ℝ) < Fintype.card X := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨xstar⟩
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B.card := by
    have : 0 < κ * (Fintype.card X : ℝ) := mul_pos hκ hn
    linarith
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; exact_mod_cast hBpos
  refine ⟨dtf_nonexp B hB, ?_⟩
  set n : ℝ := (Fintype.card X : ℝ) with hndef
  set D := distSum X with hD
  set Δ := avgDist X with hΔ
  set f := distToFinset B with hf
  have hDΔ : n ^ 2 * Δ = D := by
    rw [hΔ, avgDist, ← hD, ← hndef]; field_simp
  have hc0 : 0 < c := by linarith
  -- T
  set T : ℝ := ∑ y : X, dist y xstar with hT
  have hDT : D ≤ 2 * n * T := by
    have h1 : D ≤ ∑ x : X, ∑ y : X, (dist x xstar + dist y xstar) := by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro y _
      have := dist_triangle x xstar y
      rw [dist_comm xstar y] at this; exact this
    have h2 : ∑ x : X, ∑ y : X, (dist x xstar + dist y xstar) = 2 * n * T := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, hT, hndef]; ring
    linarith
  -- f lower bound
  have hfy : ∀ y, dist y xstar - Δ / c ≤ f y := by
    intro y
    rw [hf, dtf_eq B hB]
    apply Finset.le_inf'
    intro b hb
    have hb' : dist xstar b < Δ / c := by
      have := (Finset.mem_filter.mp hb).2; exact this
    have := dist_triangle y b xstar
    rw [dist_comm b xstar] at this
    linarith
  have hsumf : T - n * (Δ / c) ≤ ∑ y, f y := by
    have : ∑ y : X, (dist y xstar - Δ / c) ≤ ∑ y, f y := Finset.sum_le_sum (fun y _ => hfy y)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [hT]; rw [hndef]; linarith
  have hf0 : ∀ b ∈ B, f b = 0 := by
    intro b hb
    have h1 := dtf_le_dist B hB b b hb
    have h2 := dtf_nonneg B hB b
    rw [dist_self] at h1
    exact le_antisymm h1 h2
  have hfnn : ∀ y, 0 ≤ f y := fun y => dtf_nonneg B hB y
  -- spread
  have hSf : (B.card : ℝ) * ∑ y, f y ≤ lineSpread f / 2 := by
    have hsplit : lineSpread f = ∑ x ∈ B, ∑ y, |f x - f y| + ∑ x ∈ Bᶜ, ∑ y, |f x - f y| := by
      rw [lineSpread, Finset.sum_add_sum_compl]
    have hfirst : ∑ x ∈ B, ∑ y, |f x - f y| = (B.card : ℝ) * ∑ y, f y := by
      rw [Finset.sum_congr rfl (g := fun _ => ∑ y, f y)]
      · simp
      · intro x hx
        apply Finset.sum_congr rfl
        intro y _
        rw [hf0 x hx, zero_sub, abs_neg, abs_of_nonneg (hfnn y)]
    have hsecond : (B.card : ℝ) * ∑ y, f y ≤ ∑ x ∈ Bᶜ, ∑ y, |f x - f y| := by
      have h1 : ∑ x ∈ Bᶜ, ∑ y ∈ B, |f x - f y| ≤ ∑ x ∈ Bᶜ, ∑ y, |f x - f y| := by
        apply Finset.sum_le_sum; intro x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
      have h2 : ∑ x ∈ Bᶜ, ∑ y ∈ B, |f x - f y| = (B.card : ℝ) * ∑ x ∈ Bᶜ, f x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_congr rfl (g := fun _ => f x)]
        · simp
        · intro y hy
          rw [hf0 y hy, sub_zero, abs_of_nonneg (hfnn x)]
      have h3 : ∑ x ∈ Bᶜ, f x = ∑ x, f x := by
        have := Finset.sum_add_sum_compl B f
        have h0 : ∑ x ∈ B, f x = 0 := Finset.sum_eq_zero hf0
        linarith
      rw [h2, h3] at h1; exact h1
    linarith
  -- combine
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  have hSfnn : 0 ≤ ∑ y, f y := Finset.sum_nonneg (fun y _ => hfnn y)
  have hkey : n * ∑ y, f y ≥ D * (1 / 2 - 1 / c) := by
    have h1 : n * (T - n * (Δ / c)) ≤ n * ∑ y, f y := mul_le_mul_of_nonneg_left hsumf hn.le
    have h2 : n * (T - n * (Δ / c)) = n * T - D / c := by
      rw [← hDΔ]; field_simp
    have h3 : D / 2 ≤ n * T := by nlinarith
    have : D * (1 / 2 - 1 / c) = D / 2 - D / c := by ring
    linarith
  have hc1 : 0 ≤ 1 / 2 - 1 / c := by
    have : 1 / c < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hc
    linarith
  have hfinal : D * ((κ / 2) * (1 - 2 / c)) ≤ lineSpread f := by
    have e1 : κ * n * (D * (1 / 2 - 1 / c)) ≤ (B.card : ℝ) * (n * ∑ y, f y) := by
      apply mul_le_mul hdense hkey (by positivity) (by positivity)
    have e2 : n * ((B.card : ℝ) * ∑ y, f y) ≤ n * (lineSpread f / 2) :=
      mul_le_mul_of_nonneg_left hSf hn.le
    have e3 : n * (D * ((κ / 2) * (1 - 2 / c))) ≤ n * lineSpread f := by
      have : D * ((κ / 2) * (1 - 2 / c)) = κ * (D * (1 / 2 - 1 / c)) := by ring
      have hh : 0 ≤ κ * (D * (1 / 2 - 1 / c)) := by positivity
      nlinarith
    exact le_of_mul_le_mul_left e3 hn
  have hpos : 0 < (κ / 2) * (1 - 2 / c) := by
    have : 2 / c < 1 := by rw [div_lt_one hc0]; exact hc
    have : 0 < 1 - 2 / c := by linarith
    positivity
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hpos]
  exact hfinal

end EuclideanLineAvgDist

end

theorem solution : type_of% @EuclideanLineAvgDist.chk_dense_ball_embedding := @EuclideanLineAvgDist.chk_dense_ball_embedding

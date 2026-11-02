-- Prove2me | solution 1 for BubeckCO.PSGD.psgd_lipschitz_rate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:32:06.77423+00:00
-- url     : https://prove2.me/submissions/8161e388-b5b0-4614-9491-9eeb0b35116b

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj
import Definitions.Def_BubeckCO_PSGD_IsPSGDRun
import Theorems.Thm_BubeckCO_PSGD_psgd_sum_bound
set_option autoImplicit false

open BubeckCO.PSGD

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcompact : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hsub : ∀ z ∈ X, ∃ gz, IsSubgradient X f z gz)
    (R L : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) (ht : 1 ≤ t)
    (hR : ∀ z ∈ X, ‖z - x 1‖ ≤ R)
    (hL : ∀ s ∈ Finset.Icc 1 t, ‖g s‖ ≤ L)
    (hrun : IsPSGDRun X f (R / (L * Real.sqrt t)) x g t)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤ R * L / Real.sqrt t := by
  have ht_pos : (0 : ℝ) < t := by positivity
  have ht_ne : (t : ℝ) ≠ 0 := ht_pos.ne'
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsqrt_ne : Real.sqrt t ≠ 0 := hsqrt_pos.ne'
  have hcard : ((Finset.Icc 1 t).card : ℝ) = t := by
    rw [Nat.card_Icc]
    have : t + 1 - 1 = t := by omega
    rw [this]
  have hxs_mem : ∀ s ∈ Finset.Icc 1 t, x s ∈ X := by
    intro s hs
    rcases Finset.mem_Icc.mp hs with ⟨hs1, hst⟩
    exact (hrun s hs1 hst).1.1
  let xbar := (1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s
  have hxbar_mem : xbar ∈ X := by
    change (1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s ∈ X
    rw [Finset.smul_sum]
    refine hXconv.sum_mem (fun s _ => by positivity) ?_ hxs_mem
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
  rcases hsub xbar hxbar_mem with ⟨gbar, hgbar⟩
  have hjensen : (t : ℝ) * (f xbar - f xstar) ≤ ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) := by
    have h_le : ∑ s ∈ Finset.Icc 1 t, (f xbar - f (x s)) ≤
        ∑ s ∈ Finset.Icc 1 t, inner ℝ gbar (xbar - x s) :=
      Finset.sum_le_sum fun s hs => hgbar.2 (x s) (hxs_mem s hs)
    have h_rhs : ∑ s ∈ Finset.Icc 1 t, inner ℝ gbar (xbar - x s) = 0 := by
      rw [← inner_sum]
      have h_zero : ∑ s ∈ Finset.Icc 1 t, (xbar - x s) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hcard]
        dsimp [xbar]
        rw [smul_smul, mul_one_div_cancel ht_ne, one_smul, sub_self]
      rw [h_zero, inner_zero_right]
    have h_lhs : ∑ s ∈ Finset.Icc 1 t, (f xbar - f (x s)) =
        (t : ℝ) * (f xbar - f xstar) - ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
        nsmul_eq_mul, nsmul_eq_mul, hcard]
      ring
    linarith
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg _) (hR xstar hxstar)
  have h1_mem : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨le_rfl, ht⟩
  have hL_nonneg : 0 ≤ L := le_trans (norm_nonneg _) (hL 1 h1_mem)
  rcases eq_or_lt_of_le hR_nonneg with rfl | hR_pos
  · have hxbar_eq : xbar = x 1 := sub_eq_zero.mp (norm_le_zero_iff.mp (hR xbar hxbar_mem))
    have hxstar_eq : xstar = x 1 := sub_eq_zero.mp (norm_le_zero_iff.mp (hR xstar hxstar))
    change f xbar - f xstar ≤ 0 * L / Real.sqrt t
    rw [hxbar_eq, hxstar_eq, sub_self, zero_mul, zero_div]
  rcases eq_or_lt_of_le hL_nonneg with rfl | hL_pos
  · have h_sum_nonpos : ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤ 0 := by
      refine Finset.sum_nonpos fun s hs => ?_
      rcases Finset.mem_Icc.mp hs with ⟨hs1, hst⟩
      have hgs_zero : g s = 0 := norm_le_zero_iff.mp (hL s hs)
      have h_subgrad := (hrun s hs1 hst).1.2 xstar hxstar
      rw [hgs_zero, inner_zero_left] at h_subgrad
      exact h_subgrad
    have h_f_nonpos : f xbar - f xstar ≤ 0 := by
      nlinarith
    change f xbar - f xstar ≤ R * 0 / Real.sqrt t
    rw [mul_zero, zero_div]
    exact h_f_nonpos
  · let η := R / (L * Real.sqrt t)
    have hη_pos : 0 < η := by positivity
    have h_sum := psgd_sum_bound X hXcompact hXconv f R L η hη_pos x g t ht hR hL hrun xstar hxstar
    have h_sq_sqrt : Real.sqrt t ^ 2 = (t : ℝ) := Real.sq_sqrt ht_pos.le
    have h_rhs_eq : R ^ 2 / (2 * η) + η * L ^ 2 * (t : ℝ) / 2 =
        (t : ℝ) * (R * L / Real.sqrt t) := by
      dsimp [η]
      have hL_ne : L ≠ 0 := hL_pos.ne'
      have hR_ne : R ≠ 0 := hR_pos.ne'
      field_simp
      nlinarith [h_sq_sqrt]
    rw [h_rhs_eq] at h_sum
    have h_prod : (t : ℝ) * (f xbar - f xstar) ≤ (t : ℝ) * (R * L / Real.sqrt t) :=
      le_trans hjensen h_sum
    exact le_of_mul_le_mul_left h_prod ht_pos

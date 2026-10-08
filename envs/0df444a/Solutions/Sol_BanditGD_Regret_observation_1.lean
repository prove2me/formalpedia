-- Prove2me | solution 1 for BanditGD.Regret.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:35:03.486326+00:00
-- url     : https://prove2.me/submissions/f71385e5-e8bc-4455-965f-21aa248fc9d1

import Mathlib
open scoped Pointwise

set_option autoImplicit false


theorem BanditGD_obs1_pt {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S) (C : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ConvexOn ℝ S f) (hbdd : ∀ x ∈ S, |f x| ≤ C)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S) :
    f ((1 - α) • x) ≤ f x + 2 * α * C := by
  have h := hconv.2 hx h0S (show (0:ℝ) ≤ 1 - α by linarith) hα0 (show 1 - α + α = 1 by ring)
  simp only [smul_zero, add_zero, smul_eq_mul] at h
  have h1 := abs_le.mp (hbdd x hx)
  have h2 := abs_le.mp (hbdd 0 h0S)
  have h3 : α * (f 0 - f x) ≤ α * (2 * C) :=
    mul_le_mul_of_nonneg_left (by linarith) hα0
  nlinarith

open scoped Pointwise in
theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (h0S : (0 : EuclideanSpace ℝ (Fin d)) ∈ S) (C : ℝ) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    (⨅ x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))), ∑ t ∈ Finset.Icc 1 n, c t x)
      ≤ 2 * α * C * n + ⨅ x : S, ∑ t ∈ Finset.Icc 1 n, c t x := by
  have hsub : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) ⊆ S := by
    rintro y ⟨x, hx, rfl⟩
    exact hSconv.smul_mem_of_zero_mem h0S hx ⟨by linarith, by linarith⟩
  have hlow : ∀ x ∈ S, -(n * C) ≤ ∑ t ∈ Finset.Icc 1 n, c t x := by
    intro x hx
    have : ∑ t ∈ Finset.Icc 1 n, (-C) ≤ ∑ t ∈ Finset.Icc 1 n, c t x :=
      Finset.sum_le_sum fun t _ => (abs_le.mp (hcbdd t x hx)).1
    simpa [Finset.sum_const, Nat.card_Icc] using this
  have hbdd : BddBelow (Set.range fun x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) =>
      ∑ t ∈ Finset.Icc 1 n, c t x) := by
    refine ⟨-(n * C), ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hlow y (hsub y.2)
  have : Nonempty S := ⟨⟨0, h0S⟩⟩
  have key : ∀ x : S, (⨅ x : ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))),
      ∑ t ∈ Finset.Icc 1 n, c t x) - 2 * α * C * n ≤ ∑ t ∈ Finset.Icc 1 n, c t x := by
    rintro ⟨x, hx⟩
    have hmem : (1 - α) • x ∈ ((1 - α) • S : Set (EuclideanSpace ℝ (Fin d))) :=
      Set.smul_mem_smul_set hx
    have h1 := ciInf_le hbdd ⟨(1 - α) • x, hmem⟩
    have h2 : ∑ t ∈ Finset.Icc 1 n, c t ((1 - α) • x) ≤
        ∑ t ∈ Finset.Icc 1 n, (c t x + 2 * α * C) :=
      Finset.sum_le_sum fun t _ =>
        BanditGD_obs1_pt S h0S C (c t) (hcconv t) (hcbdd t) α hα0 hα1 x hx
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc] at h2
    simp only [nsmul_eq_mul, Nat.add_sub_cancel] at h2
    simp only at h1 ⊢
    nlinarith
  have := le_ciInf key
  linarith

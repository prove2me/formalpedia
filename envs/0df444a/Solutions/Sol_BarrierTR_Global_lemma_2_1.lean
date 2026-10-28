-- Prove2me | solution 1 for BarrierTR.Global.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:50:58.306031+00:00
-- url     : https://prove2.me/submissions/807affea-8e3e-42c3-bead-fcc4d7c4f1c0

import Mathlib
open scoped RealInnerProductSpace
open Filter Topology

theorem solution {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (q : V) (Q : V →ₗ[ℝ] V) (hQ : Q.IsSymmetric) (L : V →ₗ[ℝ] W) (hL : L ≠ 0)
    (T : Seminorm ℝ W) (hT : ∀ w, T w = 0 → w = 0) (Δ : ℝ) (hΔ : 0 < Δ)
    (d : V) (hqd : ⟪q, d⟫ ≤ 0) (hLd : L d ≠ 0) :
    (if ⟪d, Q d⟫ ≤ 0 then |⟪q, d⟫| / 2 * (Δ / T (L d))
      else |⟪q, d⟫| / 2 * min (Δ / T (L d)) (|⟪q, d⟫| / ⟪d, Q d⟫))
      ≤ -sInf {y : ℝ | ∃ α : ℝ, T (α • L d) ≤ Δ ∧
          y = ⟪q, α • d⟫ + (1 / 2) * ⟪α • d, Q (α • d)⟫} := by
  obtain ⟨a, ha⟩ : ∃ a, a = ⟪q, d⟫ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ⟪d, Q d⟫ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = T (L d) := ⟨_, rfl⟩
  have hτpos : 0 < τ := by
    rcases (apply_nonneg T (L d)).lt_or_eq with h | h
    · rw [hτ]; exact h
    · exact absurd (hT _ h.symm) hLd
  have hkey : ∀ α : ℝ, ⟪q, α • d⟫ + (1 / 2) * ⟪α • d, Q (α • d)⟫ = α * a + 1 / 2 * α ^ 2 * b := by
    intro α
    rw [map_smul, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, ha, hb]
    ring
  have hTs : ∀ α : ℝ, T (α • L d) = |α| * τ := by
    intro α; rw [map_smul_eq_mul, Real.norm_eq_abs, hτ]
  have haabs : |a| = -a := abs_of_nonpos (ha ▸ hqd)
  rw [← ha, ← hb, ← hτ]
  set Y := {y : ℝ | ∃ α : ℝ, T (α • L d) ≤ Δ ∧
          y = ⟪q, α • d⟫ + (1 / 2) * ⟪α • d, Q (α • d)⟫} with hY
  have hbdd : BddBelow Y := by
    refine ⟨-(Δ / τ) * |a| - 1 / 2 * (Δ / τ) ^ 2 * |b|, ?_⟩
    rintro y ⟨α, hα, rfl⟩
    rw [hkey]
    rw [hTs] at hα
    have hαb : |α| ≤ Δ / τ := by rw [le_div_iff₀ hτpos]; exact hα
    have h1 : -(|α| * |a|) ≤ α * a := by rw [← abs_mul]; exact neg_abs_le _
    have h2 : -(α ^ 2 * |b|) ≤ α ^ 2 * b := by
      have := neg_abs_le b
      nlinarith [sq_nonneg α]
    have h3 : |α| * |a| ≤ Δ / τ * |a| := mul_le_mul_of_nonneg_right hαb (abs_nonneg a)
    have h4 : α ^ 2 ≤ (Δ / τ) ^ 2 := by
      rw [← sq_abs α]; exact pow_le_pow_left₀ (abs_nonneg α) hαb 2
    have h5 : α ^ 2 * |b| ≤ (Δ / τ) ^ 2 * |b| := mul_le_mul_of_nonneg_right h4 (abs_nonneg b)
    nlinarith
  have hmem : ∀ α : ℝ, 0 ≤ α → α ≤ Δ / τ → α * a + 1 / 2 * α ^ 2 * b ∈ Y := by
    intro α h0 h1
    refine ⟨α, ?_, (hkey α).symm⟩
    rw [hTs, abs_of_nonneg h0]
    rwa [le_div_iff₀ hτpos] at h1
  apply le_neg.mpr
  have hD : 0 < Δ / τ := div_pos hΔ hτpos
  split_ifs with hb0
  · refine (csInf_le hbdd (hmem (Δ / τ) hD.le le_rfl)).trans ?_
    rw [haabs]
    nlinarith [sq_nonneg (Δ / τ)]
  · push_neg at hb0
    set mm := min (Δ / τ) (|a| / b) with hmm
    have hm0 : 0 ≤ mm := le_min hD.le (div_nonneg (abs_nonneg a) hb0.le)
    have hm1 : mm ≤ Δ / τ := min_le_left _ _
    have hm2 : mm ≤ |a| / b := min_le_right _ _
    have hm3 : mm * b ≤ |a| := by rwa [le_div_iff₀ hb0] at hm2
    refine (csInf_le hbdd (hmem mm hm0 hm1)).trans ?_
    rw [haabs] at hm3 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hm3 hm0]

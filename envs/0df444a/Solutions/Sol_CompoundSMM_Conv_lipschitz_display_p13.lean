-- Prove2me | solution 1 for CompoundSMM.Conv.lipschitz_display_p13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:41:17.308653+00:00
-- url     : https://prove2.me/submissions/83ae4808-e35e-4371-8284-27ea6a7d0422

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting
open CompoundSMM.Conv

theorem solution {n ℓG ℓF ℓφ : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ : ℝ) (hA2 : A2 P Lψ Lφ)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (L : Ξ → ℝ) (ξs ηs : ℕ → Ξ) (x : E n)
    (gs ginf : ℕ → E n → E ℓG) (fs finf : ℕ → E n → E ℓF)
    (h13G : ∀ t < N, ‖gs t x - ginf t x‖ ≤ ε * L (ξs t))
    (h13F : ∀ s < N, ‖fs s x - finf s x‖ ≤ ε * L (ηs s)) :
    |VN P N gs fs x - VN P N ginf finf x|
      ≤ Lψ * Lφ * (ε / N) *
          (∑ t ∈ Finset.range N, L (ξs t) + ∑ s ∈ Finset.range N, L (ηs s)) := by
  obtain ⟨hLψ, hLφ, -, -, hψL, hφL, -⟩ := hA2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set Fb : E ℓF := (1 / (N : ℝ)) • ∑ s ∈ Finset.range N, fs s x
  set Fi : E ℓF := (1 / (N : ℝ)) • ∑ s ∈ Finset.range N, finf s x
  -- bound on the inner averages
  have hF : ‖Fb - Fi‖ ≤ (ε / N) * ∑ s ∈ Finset.range N, L (ηs s) := by
    have : Fb - Fi = (1 / (N : ℝ)) • ∑ s ∈ Finset.range N, (fs s x - finf s x) := by
      simp only [Fb, Fi, Finset.sum_sub_distrib, smul_sub]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 1 / (N : ℝ) * ‖∑ s ∈ Finset.range N, (fs s x - finf s x)‖
        ≤ 1 / (N : ℝ) * ∑ s ∈ Finset.range N, ε * L (ηs s) := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
          exact h13F s (Finset.mem_range.mp hs)
      _ = (ε / N) * ∑ s ∈ Finset.range N, L (ηs s) := by
          rw [← Finset.mul_sum]; ring
  have hterm : ∀ t ∈ Finset.range N,
      ‖P.φ (gs t x) Fb - P.φ (ginf t x) Fi‖ ≤ Lφ * (ε * L (ξs t) + (ε / N) * ∑ s ∈ Finset.range N, L (ηs s)) := by
    intro t ht
    refine (hφL _ _ _ _).trans ?_
    gcongr
    have ha := norm_nonneg (gs t x - ginf t x)
    have hb := norm_nonneg (Fb - Fi)
    calc Real.sqrt (‖gs t x - ginf t x‖ ^ 2 + ‖Fb - Fi‖ ^ 2)
        ≤ ‖gs t x - ginf t x‖ + ‖Fb - Fi‖ := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [mul_nonneg ha hb]
      _ ≤ _ := add_le_add (h13G t (Finset.mem_range.mp ht)) hF
  unfold VN
  refine (hψL _ _).trans ?_
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc Lψ * (1 / (N : ℝ) * ‖∑ t ∈ Finset.range N, (P.φ (gs t x) Fb - P.φ (ginf t x) Fi)‖)
      ≤ Lψ * (1 / (N : ℝ) * ∑ t ∈ Finset.range N,
          Lφ * (ε * L (ξs t) + (ε / N) * ∑ s ∈ Finset.range N, L (ηs s))) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = Lψ * Lφ * (ε / N) *
          (∑ t ∈ Finset.range N, L (ξs t) + ∑ s ∈ Finset.range N, L (ηs s)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp

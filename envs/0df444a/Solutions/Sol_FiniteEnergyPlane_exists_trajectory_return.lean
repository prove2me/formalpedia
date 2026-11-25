-- Prove2me | solution 1 for FiniteEnergyPlane.exists_trajectory_return
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T10:36:55.56965+00:00
-- url     : https://prove2.me/submissions/a91de9cf-1ed8-4569-af19-588bedc822bf

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_uniform_hit_near_orbit
import Theorems.Thm_FiniteEnergyPlane_proj_not_mem_range_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_isReebTrajectory
import Theorems.Thm_FiniteEnergyPlane_exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_trajectory_return_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (u₀ : ℂ → V 1) (hu₀ : IsFastPlane H J u₀) (hu₀P : IsNondegenerateEnd H u₀ cylInf P 1)
    (hu₀e : IsEmbeddedPlane u₀) :
    ∃ y : ℝ → V 1, IsReebTrajectory H y ∧ ∃ v ∈ embeddedFastPlaneSet H J P {y 0} γ,
      ∃ τ > 0, y τ ∈ Set.range (fun z => proj H (v z)) := by
  obtain ⟨W, hW, hPW, L, -, hhit⟩ := exists_uniform_hit_near_orbit H hH J hJ P hcz u₀ hu₀ hu₀P
  -- a point of the plane near the orbit
  obtain ⟨ζ, hζ⟩ : ∃ ζ, proj H (u₀ ζ) ∈ W := by
    obtain ⟨d, c, b, hb, -, hend⟩ := hu₀P
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW (P.x c) (hPW ⟨c, rfl⟩)
    obtain ⟨s₀, hs₀⟩ := hend (ε / 2) (half_pos hε)
    have h := hs₀ (max s₀ 0) (le_max_left _ _) 0
    refine ⟨cylInf (max s₀ 0) 0, hεW ?_⟩
    simp only [endW, mul_zero, zero_add, norm_smul, Real.norm_eq_abs, Real.abs_exp] at h
    have h1 : 1 ≤ Real.exp (b * max s₀ 0) :=
      Real.one_le_exp (mul_nonneg hb.le (le_max_right _ _))
    rw [mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg (proj H (u₀ (cylInf (max s₀ 0) 0)) - P.x c)]
  have hu0 : u₀ ζ ≠ 0 := hu₀.1.2.1 ζ trivial
  have hS : proj H (u₀ ζ) ∈ energySurface H := by
    have hex : ∃ r : ℝ, 0 < r ∧ H (r • u₀ ζ) = 1 := (hH.2.1 _ hu0).exists
    unfold proj scaleToS
    rw [dif_pos hex]
    exact (Classical.choose_spec hex).2
  obtain ⟨y, hy, hy0⟩ := exists_isReebTrajectory H hH _ hS
  obtain ⟨v, hv, hvr⟩ := exists_mem_embeddedFastPlaneSet_of_isEmbeddedPlane H hH J hJ P γ hγ hγT
    u₀ hu₀ hu₀P hu₀e ζ
  obtain ⟨⟨τ, hτ, hyτ⟩, -⟩ := hhit y hy (hy0 ▸ hζ)
    (hy0 ▸ proj_not_mem_range_of_isFastPlane H hH J hJ P hcz u₀ hu₀ hu₀P hu₀e ζ)
  exact ⟨y, hy, v, hy0 ▸ hv, τ, hτ.1, hvr ▸ hyτ⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (hγ : 0 < γ) (hγT : γ < P.T)
    (hΛ : ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
      IsSeqCompactCInftyLoc (embeddedFastPlaneSet H J P K γ))
    (u₀ : ℂ → V 1) (hu₀ : IsFastPlane H J u₀) (hu₀P : IsNondegenerateEnd H u₀ cylInf P 1)
    (hu₀e : IsEmbeddedPlane u₀) :
    ∃ y : ℝ → V 1, IsReebTrajectory H y ∧ ∃ v ∈ embeddedFastPlaneSet H J P {y 0} γ,
      ∃ τ > 0, y τ ∈ Set.range (fun z => proj H (v z)) :=
  exists_trajectory_return_aux H hH J hJ P hcz γ hγ hγT u₀ hu₀ hu₀P hu₀e

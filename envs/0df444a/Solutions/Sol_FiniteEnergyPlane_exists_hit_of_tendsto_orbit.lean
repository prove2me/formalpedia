-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hit_of_tendsto_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T12:30:42.60336+00:00
-- url     : https://prove2.me/submissions/3883038d-30d2-4e13-9900-0cc203444c85

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_IsReebTrajectory_apply_not_mem_range_of_apply_zero
import Theorems.Thm_FiniteEnergyPlane_exists_uniform_hit_near_orbit



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma l69_shift {H : V 1 → ℝ} {y : ℝ → V 1} (hy : IsReebTrajectory H y) (a : ℝ) :
    IsReebTrajectory H (fun t => y (t + a)) := by
  refine ⟨fun t => hy.1 (t + a), fun t => ?_⟩
  have h2 : HasDerivAt (fun t : ℝ => t + a) 1 t := (hasDerivAt_id t).add_const a
  have h3 := HasDerivAt.scomp t (hy.2 (t + a)) h2
  rw [one_smul] at h3
  exact h3

theorem exists_hit_of_tendsto_orbit_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (hy₀ : y 0 ∉ Set.range P.x) :
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atTop ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t > n, y t ∈ Set.range (fun z => proj H (u z))) ∧
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atBot ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t < n, y t ∈ Set.range (fun z => proj H (u z))) := by
  obtain ⟨W, hWo, hPW, L, hL, hK⟩ := exists_uniform_hit_near_orbit H hH J hJ P hcz u hu huP
  have hoff := IsReebTrajectory.apply_not_mem_range_of_apply_zero hH P hy hy₀
  have hmem : ∀ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀)) →
      ∀ᶠ k in atTop, y (s k) ∈ W := fun τ₀ s hs =>
    hs.eventually (hWo.mem_nhds (hPW ⟨τ₀, rfl⟩))
  constructor
  · rintro ⟨τ₀, s, hs, hys⟩ n
    obtain ⟨k, hk1, hk2⟩ := ((hmem τ₀ s hys).and (hs.eventually_gt_atTop n)).exists
    have h := (hK (fun t => y (t + s k)) (l69_shift hy (s k)) (by simpa using hk1)
      (by simpa using hoff (s k))).1
    obtain ⟨t, ⟨ht0, -⟩, hyt⟩ := h
    exact ⟨t + s k, by linarith, hyt⟩
  · rintro ⟨τ₀, s, hs, hys⟩ n
    obtain ⟨k, hk1, hk2⟩ := ((hmem τ₀ s hys).and (hs.eventually_lt_atBot n)).exists
    have h := (hK (fun t => y (t + s k)) (l69_shift hy (s k)) (by simpa using hk1)
      (by simpa using hoff (s k))).2
    obtain ⟨t, ⟨-, ht0⟩, hyt⟩ := h
    exact ⟨t + s k, by linarith, hyt⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1) (hu : IsFastPlane H J u)
    (huP : IsNondegenerateEnd H u cylInf P 1) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (hy₀ : y 0 ∉ Set.range P.x) :
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atTop ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t > n, y t ∈ Set.range (fun z => proj H (u z))) ∧
    ((∃ (τ₀ : ℝ) (s : ℕ → ℝ), Tendsto s atTop atBot ∧ Tendsto (y ∘ s) atTop (𝓝 (P.x τ₀))) →
      ∀ n : ℝ, ∃ t < n, y t ∈ Set.range (fun z => proj H (u z))) :=
  FiniteEnergyPlane.exists_hit_of_tendsto_orbit_glue H hH J hJ P hcz u hu huP y hy hy₀

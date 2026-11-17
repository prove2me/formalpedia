-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jHolomorphic_family_of_window
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T13:02:59.792333+00:00
-- url     : https://prove2.me/submissions/246cb237-4bf1-4fc8-9ee0-76c11465d6b1

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_exists_stdTube_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_jbar_family_of_window
import Theorems.Thm_FiniteEnergyPlane_exists_jHolomorphic_family_of_stdTube
import Mathlib

/-!
# Reduction of `exists_jHolomorphic_family_of_window` to its children

A standard tube `Φ` around `u` turns the window at `δ` for `A_P` into the window for the tube loop
`Sinf`, with windings shifted by one; the `Jbar`-holomorphic family `G` with normal velocity `i`
is then transferred to the symplectization.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Glue: the family for a given rate from the tube, the family in the tube, and the transfer. -/
theorem exists_jHolomorphic_family_of_window_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (δ : ℝ) (hδ : δ < 0) (hδe : ∀ v, ¬ IsAsymptoticEigen J P δ v)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
        JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
      (∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
        IsCylCloseTo H ε (fun z => g (z, t)) u := by
  obtain ⟨ρ, hρ, b, hb, Φ, Jbar, Jinf, Sinf, hstd, hΦ, hΦu, hΦp, hτ, hmodel, heig, hwind⟩ :=
    exists_stdTube_of_isFastPlane H hH J hJ P u hu huP
  -- the window in the tube frame: windings shift by one
  have hδe' : ∀ e, ¬ IsLoopEigen Sinf δ e := fun e he => by
    obtain ⟨v, hv⟩ := heig δ e he
    exact hδe v hv
  have hwin' : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k →
      (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k) := fun μ k h => by
    rcases hwin μ (k + 1) (hwind μ k h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  obtain ⟨r, hr, G, hG, hG0, hGω, hGt, hGc⟩ :=
    exists_jbar_family_of_window ρ b hρ hb Jbar Jinf Sinf hstd δ hδ hδe' hwin' l hl Complex.I
  exact exists_jHolomorphic_family_of_stdTube H hH J hJ P u hu huP δ hδ hwin l hl ρ b hρ hb Φ Jbar
    hΦ hΦu hΦp hτ hmodel r hr G hG hG0 hGω hGt hGc

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) (δ : ℝ) (hδ : δ < 0) (hδe : ∀ v, ¬ IsAsymptoticEigen J P δ v)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ r > 0, ∃ g : ℂ × ℝ → V 1, ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r) ∧
      (∀ z, g (z, 0) = u z) ∧
      (∀ t ∈ Set.Ioo (-r) r,
        ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
        JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t)) ∧
        IsNondegenerateEnd H (fun z => g (z, t)) cylInf P 1 ∧
        (∃ C : ℝ, ∀ z, infDist (proj H (g (z, t))) (Set.range P.x) ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π))) ∧
        ∃ C : ℝ, ∀ z, ∃ Δ : ℂ, ‖fderiv ℝ g (z, t) (Δ, 1)‖ ≤
          C * (1 + ‖z‖) ^ (δ / (2 * π)) * ‖g (z, t)‖) ∧
      (∀ (Δ : ℂ) (δt lam : ℝ), fderiv ℝ g (0, 0) (Δ, δt) + lam • g (0, 0) = 0 →
        Δ = 0 ∧ δt = 0 ∧ lam = 0) ∧
      ∀ ε > 0, ∃ r' ∈ Set.Ioc 0 r, ∀ t ∈ Set.Ioo (-r') r',
        IsCylCloseTo H ε (fun z => g (z, t)) u :=
  exists_jHolomorphic_family_of_window_aux H hH J hJ P hcz u hu huP hue δ hδ hδe hwin l hl

-- Prove2me | solution 1 for EdenPalomar.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:51.28792+00:00
-- url     : https://prove2.me/submissions/d39dfc54-3f3c-486b-9f81-6fe0795d0187

import Definitions.Def_Eden_Solution
import Definitions.Def_PalomarSolution
import Theorems.Thm_EdenVerified_main_theorem
import Theorems.Thm_Eden_finiteTimeDimension_isGreatest


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open EdenPalomar
namespace EdenPalomar
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    ∃ φ : ℝ → PhaseSpace → PhaseSpace,
    (∀ p, φ 0 p = p ∧ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun τ => φ τ p) (vectorField c (φ t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => φ t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p, φ (s + t) p = φ t (φ s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (φ t)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ p, Function.Bijective (fderiv ℝ (φ t) p)) ∧
    IsGlobalAttractor φ attractor ∧
    (∀ p, divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 -
      6 * (radiusSq₂ p - 1) ^ 2 ∧ divergence c p ≤ 4 - c ∧ 4 - c < 0) ∧
    (4 < 4 + 4 / c ∧ 4 + 4 / c < 5) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' attractor) (4 + 4 / c) ∧
      {p ∈ attractor | finiteTimeDimension φ t p = 4 + 4 / c} = torus) ∧
    (∀ p ∈ attractor, ∀ i : Fin 5,
      Tendsto (fun t : ℝ => Real.log ((fderiv ℝ (φ t) p).toLinearMap.singularValues i) / t)
        atTop (𝓝 (lyapunovExponent φ p i))) ∧
    (globalLyapunovDimension φ attractor = 4 + 4 / c) ∧
    IsGreatest (asymptoticDimension φ '' attractor) (4 + 4 / c) ∧
    ({p ∈ attractor | asymptoticDimension φ p = 4 + 4 / c} = torus) ∧
    IsGreatest (asymptoticDimension φ '' periodicEquilibriumSet c φ) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension φ t '' periodicEquilibriumSet c φ) 3) ∧
    (∀ (t : ℝ) (p : PhaseSpace), p ∈ torus → φ t p ∈ torus) ∧
    (∀ p ∈ torus, ∀ t : ℝ, 0 < t → φ t p ≠ p) ∧
    (∀ t θ₁ θ₂ : ℝ, φ t (torusPoint θ₁ θ₂) =
      torusPoint (θ₁ + t) (θ₂ + Real.sqrt 2 * t)) ∧
    (∀ p ∈ attractor, Tendsto (fun t : ℝ => finiteTimeDimension φ t p)
      atTop (𝓝 (asymptoticDimension φ p))) ∧
    (∀ t : ℝ, 0 < t → ∀ p,
      IsGreatest (admissibleDimensions φ t p) (finiteTimeDimension φ t p)) := by
  rcases EdenVerified.main_theorem c hc with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  exact ⟨Eden.evolution c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, fun t ht p => Eden.finiteTimeDimension_isGreatest c ht.le p⟩
end EdenPalomar

-- Prove2me | solution 1 for FriedCrossing.TwinRate.twin_rate_of_cluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:56:43.18043+00:00
-- url     : https://prove2.me/submissions/eb8ec7d6-133b-4f86-9ff1-ddec7f66bdd6

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_at_cddp
import Theorems.Thm_FriedCrossing_TwinRate_hasDerivAt_twin
import Theorems.Thm_FriedCrossing_TwinRate_continuousAt_wPlus
import Theorems.Thm_FriedCrossing_TwinRate_continuousAt_dwPlus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution (sStar : ℝ → ℝ) (a b a' b' : ℝ → ℝ → ℝ) {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hderiv_a : ∀ θ τ, HasDerivAt (a θ) (a' θ τ) τ)
    (hderiv_b : ∀ θ τ, HasDerivAt (b θ) (b' θ τ) τ)
    (hcont_a : ContinuousAt (Function.uncurry a) (0, 0))
    (hcont_b : ContinuousAt (Function.uncurry b) (0, 0))
    (hcont_a' : ContinuousAt (Function.uncurry a') (0, 0))
    (hcont_b' : ContinuousAt (Function.uncurry b') (0, 0))
    (ha0 : a 0 0 = r₀) (hb0 : b 0 0 = 0) :
    ∃ ε > 0, ∀ θ τ : ℝ, |θ| < ε → |τ| < ε →
      0 < disc (a θ τ) (b θ τ) ∧
      HasDerivAt (twin sStar a b θ) (dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ) τ ∧
      r₀ / 2 ≤ dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ∧
      dtwin (a θ τ) (b θ τ) (a' θ τ) (b' θ τ) τ ≤ 2 * r₀ := by
  -- the data map (θ,τ) ↦ (a, b, a', b') and the discriminant along it
  set Φ : ℝ × ℝ → ℝ × ℝ × ℝ × ℝ :=
    fun p => (a p.1 p.2, b p.1 p.2, a' p.1 p.2, b' p.1 p.2) with hΦ
  have hΦc : ContinuousAt Φ (0, 0) :=
    hcont_a.prodMk (hcont_b.prodMk (hcont_a'.prodMk hcont_b'))
  have hdisc0 : 0 < disc (a 0 0) (b 0 0) := by
    rw [ha0, hb0]; unfold disc; nlinarith
  have hdiscc : ContinuousAt (fun p : ℝ × ℝ => disc (a p.1 p.2) (b p.1 p.2)) (0, 0) := by
    unfold disc
    have h1 : ContinuousAt (fun p : ℝ × ℝ => a p.1 p.2) (0, 0) := hcont_a
    have h2 : ContinuousAt (fun p : ℝ × ℝ => b p.1 p.2) (0, 0) := hcont_b
    exact (h1.pow 2).sub (continuousAt_const.mul h2)
  -- eventually positive discriminant
  have hev1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), 0 < disc (a p.1 p.2) (b p.1 p.2) :=
    hdiscc.eventually (lt_mem_nhds hdisc0)
  -- the derivative expression as a function of (θ,τ), continuous at (0,0), value r₀
  set D : ℝ × ℝ → ℝ := fun p => dtwin (a p.1 p.2) (b p.1 p.2) (a' p.1 p.2) (b' p.1 p.2) p.2
    with hD
  have hDc : ContinuousAt D (0, 0) := by
    have hw : ContinuousAt (fun p : ℝ × ℝ => wPlus (a p.1 p.2) (b p.1 p.2)) (0, 0) := by
      have hab : ContinuousAt (fun p : ℝ × ℝ => (a p.1 p.2, b p.1 p.2)) (0, 0) :=
        hcont_a.prodMk hcont_b
      exact (continuousAt_wPlus _).comp hab
    have hdw : ContinuousAt (fun p : ℝ × ℝ => dwPlus (a p.1 p.2) (b p.1 p.2) (a' p.1 p.2)
        (b' p.1 p.2)) (0, 0) := by
      have := (continuousAt_dwPlus (p := Φ (0, 0)) hdisc0).comp hΦc
      exact this
    have hτ : ContinuousAt (fun p : ℝ × ℝ => p.2) (0, 0) := continuousAt_snd
    exact hw.add (hτ.mul hdw)
  have hD0 : D (0, 0) = r₀ := by
    simp only [hD, dtwin, ha0, hb0, zero_mul, add_zero]
    exact wPlus_at_cddp hr₀
  have hev2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), D p ∈ Set.Ioo (r₀ / 2) (2 * r₀) := by
    apply hDc.eventually
    rw [hD0]
    exact Ioo_mem_nhds (by linarith) (by linarith)
  -- extract a ball
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  refine ⟨ε, hε, fun θ τ hθ hτ => ?_⟩
  have hmem : dist ((θ, τ) : ℝ × ℝ) (0, 0) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
    exact max_lt hθ hτ
  obtain ⟨hpos, hgt⟩ := hball hmem
  exact ⟨hpos, hasDerivAt_twin (hderiv_a θ τ) (hderiv_b θ τ) hpos, hgt.1.le, hgt.2.le⟩
end FriedCrossing.TwinRate

-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_slice_deriv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T22:48:43.783985+00:00
-- url     : https://prove2.me/submissions/aff57413-7623-489e-a72b-a0d92c32abca

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_halfCyl_coeff_bounds
import Theorems.Thm_FiniteEnergyPlane_halfCyl_slice_deriv_sq_le_of_logDeriv_bound
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_tendsto_rayleigh

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory

/-! Glue for `FiniteEnergyPlane.halfCyl_slice_deriv_sq_le` (Wendl, Lemma 4.8.8). -/


namespace FiniteEnergyPlane

theorem halfCyl_slice_deriv_sq_le_aux {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤ M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
  obtain ⟨s₀, c, hs₀, hb⟩ := halfCyl_coeff_bounds S hS Sinf hSinf hSinf' hSas
  obtain ⟨μ, -, s₂, -, hF, hα, -⟩ :=
    halfCyl_exists_tendsto_rayleigh S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth
  -- the Rayleigh quotient is eventually within `1` of its limit
  obtain ⟨s₃, hs₃⟩ := (Metric.tendsto_atTop.1 hα) 1 one_pos
  have hb2 : ∀ s ≥ max s₂ s₃, |∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫| ≤
      (|μ| + 1) * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
    intro s hs
    have hFs := hF s ((le_max_left _ _).trans hs)
    have h := hs₃ s ((le_max_right _ _).trans hs)
    rw [Real.dist_eq] at h
    set D := ∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫
    set F := ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2
    have hq : |D / F| ≤ |μ| + 1 := by
      have := abs_sub_abs_le_abs_sub (D / F) μ
      linarith
    rw [abs_div, abs_of_pos hFs, div_le_iff₀ hFs] at hq
    exact hq
  exact halfCyl_slice_deriv_sq_le_of_logDeriv_bound S hS hSper ζ hζ (max s₀ (max s₂ s₃)) c (|μ| + 1)
    (lt_max_of_lt_left hs₀) (fun s hs => hb s ((le_max_left _ _).trans hs))
    (fun s hs => hb2 s ((le_max_right _ _).trans hs))

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤ M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 :=
  FiniteEnergyPlane.halfCyl_slice_deriv_sq_le_aux S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth

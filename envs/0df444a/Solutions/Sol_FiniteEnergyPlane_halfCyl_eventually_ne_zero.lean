-- Prove2me | solution 1 for FiniteEnergyPlane.halfCyl_eventually_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T22:25:39.101869+00:00
-- url     : https://prove2.me/submissions/fe099ef8-798e-49ca-b332-418b0e8a019a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
import Theorems.Thm_FiniteEnergyPlane_halfCyl_exists_subseq_tendsto_eigen



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem halfCyl_eventually_ne_zero_aux {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ζ (s, t) ≠ 0 := by
  obtain ⟨μ, -, -, -, hW⟩ := halfCyl_exists_subseq_tendsto_eigen S hS hSper Sinf hSinf hSinf'
    hSas ζ hζ hne C δ₀ hgrowth
  by_contra hcon
  push_neg at hcon
  choose σ hσ τ hτ using fun k : ℕ => hcon (k : ℝ)
  have hσt : Tendsto σ atTop atTop :=
    tendsto_atTop_mono (fun k => (hσ k).le) tendsto_natCast_atTop_atTop
  obtain ⟨φ, -, e, he, hconv⟩ := hW σ hσt
  have hmem : ∀ k, Int.fract (τ (φ k)) ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨t₀, -, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  -- the normalized slices vanish at `fract (τ (φ k))`
  have hper : ∀ s t : ℝ, ζ (s, Int.fract t) = ζ (s, t) := by
    intro s t
    have hp : Function.Periodic (fun x => ζ (s, x)) 1 := fun x => hζ.2.1 s x
    have := hp.sub_int_mul_eq (n := ⌊t⌋) (x := t)
    simp only [mul_one] at this
    exact this
  set G : ℕ → ℝ → CauchyRiemannIndex.Vec n := fun k t =>
    (Real.sqrt (∫ x in (0:ℝ)..1, ‖ζ (σ (φ k), x)‖ ^ 2))⁻¹ • ζ (σ (φ k), t) with hG
  have hzero : ∀ k, G (ψ k) (Int.fract (τ (φ (ψ k)))) = 0 := by
    intro k
    simp only [hG, hper, hτ, smul_zero]
  have hconv' : TendstoUniformly (fun k t => G (ψ k) t) e atTop :=
    fun u hu => hψ.tendsto_atTop.eventually (hconv u hu)
  have hcont : Continuous e := he.1.continuous
  have hlim' : Tendsto (fun k => G (ψ k) (Int.fract (τ (φ (ψ k))))) atTop (𝓝 (e t₀)) :=
    hconv'.tendsto_comp hcont.continuousAt hlim
  simp only [hzero] at hlim'
  have h0 : e t₀ = 0 := tendsto_nhds_unique hlim' tendsto_const_nhds
  exact isLoopEigen_apply_ne_zero Sinf hSinf.1 μ e he t₀ h0

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
    ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ζ (s, t) ≠ 0 :=
  halfCyl_eventually_ne_zero_aux S hS hSper Sinf hSinf hSinf' hSas ζ hζ hne C δ₀ hgrowth

-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_finitec2_cap_ode_derivative_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:30:09.13774+00:00
-- url     : https://prove2.me/submissions/f4b410d0-466b-4d4c-bad3-b98200e3073f

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology
noncomputable section

/-- On a finite cap band, a one-sided linear differential estimate
    bounds the Gaussian HJB gradient uniformly up to the cap. -/
theorem solution
    (p dp : ℝ → ℝ) (u C β ε : ℝ)
    (huC : u < C) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hp0 : 0 ≤ p u)
    (hpcont : ContinuousOn p (Ico u C))
    (hpderiv : ∀ y ∈ Ico u C, HasDerivAt p (dp y) y)
    (hpODE : ∀ y ∈ Ico u C, dp y ≤ β * p y + ε) :
    ∃ B : ℝ, ∀ y ∈ Ico u C, p y ≤ B := by
  classical
  refine ⟨gronwallBound (p u) β ε (C - u), ?_⟩
  intro y hy
  have hsub : Icc u y ⊆ Ico u C := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hcontinuity : ContinuousOn p (Icc u y) := hpcont.mono hsub
  have hlim : ∀ z ∈ Ico u y, ∀ r, dp z < r →
      ∃ᶠ s in 𝓝[>] z, (s - z)⁻¹ * (p s - p z) < r := by
    intro z hz r hr
    have hzcap : z ∈ Ico u C := ⟨hz.1, lt_trans hz.2 hy.2⟩
    have hfilt : (𝓝[>] z) ≤ (𝓝[≠] z) := by
      apply nhdsWithin_mono
      intro s hs
      simpa using (ne_of_gt hs)
    have hto : Tendsto (slope p z) (𝓝[>] z) (𝓝 (dp z)) :=
      (hpderiv z hzcap).tendsto_slope.mono_left hfilt
    have hev : ∀ᶠ s in 𝓝[>] z, slope p z s < r :=
      hto.eventually (eventually_lt_nhds hr)
    simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using hev.frequently
  have hbound : ∀ z ∈ Ico u y, dp z ≤ β * p z + ε := by
    intro z hz
    exact hpODE z ⟨hz.1, lt_trans hz.2 hy.2⟩
  have hG := le_gronwallBound_of_liminf_deriv_right_le
    (f := p) (f' := dp) (δ := p u) (K := β) (ε := ε)
    (a := u) (b := y) hcontinuity hlim (le_refl _) hbound
  calc
    p y ≤ gronwallBound (p u) β ε (y - u) :=
      hG y ⟨hy.1, le_rfl⟩
    _ ≤ gronwallBound (p u) β ε (C - u) :=
      (gronwallBound_mono hp0 hε hβ) (sub_le_sub_right (le_of_lt hy.2) u)

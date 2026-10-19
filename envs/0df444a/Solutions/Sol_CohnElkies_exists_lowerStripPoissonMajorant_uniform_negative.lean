-- Prove2me | solution 1 for CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/88074625-8e69-4770-a3ae-3be2d9cd1fc3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_eventually_lowerPoissonEndpointSharpCoefficient_neg
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_dimension_centered_max
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_dimension_central_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ s : ℝ,
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ s ≤
              -γ * ((d : ℝ) / 2) := by
  have hnegative :=
    eventually_lowerPoissonEndpointSharpCoefficient_neg
      hc hsharp
  have hpositive : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hless : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  obtain ⟨σ, hσpos, hσless, hσnegative⟩ :=
    (hpositive.and (hless.and hnegative)).exists
  have hmass := stripBottomMass_pos hσless
  let A : ℝ :=
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
      lowerPoissonEndpointExpectation σ
  have hA : A < 0 := hσnegative
  let γ : ℝ := -(stripBottomMass σ * A) / 2
  have hγ : 0 < γ := by
    try dsimp [γ]
    nlinarith [mul_neg_of_pos_of_neg hmass hA]
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hγscale : Tendsto
      (fun d : ℕ => γ * ((d : ℝ) / 2)) atTop atTop := by
    have hmul := hscale.atTop_mul_const hγ
    convert! hmul using 1
    ext d
    ring
  have herror : ∀ᶠ d : ℕ in atTop,
      lowerRiemannPoissonError σ ≤
        γ * ((d : ℝ) / 2) :=
    hγscale.eventually
      (Ici_mem_atTop (lowerRiemannPoissonError σ))
  refine ⟨σ, γ, hσpos, hσless, hγ, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ), herror]
    with d hd hderr
  intro s
  have hcenter := lowerStripPoissonMajorant_dimension_centered_max
    hd hc (by linarith) hσless s
  have hbound :=
    lowerStripPoissonMajorant_dimension_central_bound
      hd hc hσpos.le hσless
  calc
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ s ≤
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 := hcenter
    _ ≤ ((d : ℝ) / 2) * stripBottomMass σ * A +
      lowerRiemannPoissonError σ := hbound
    _ ≤ -γ * ((d : ℝ) / 2) := by
      try dsimp [γ] at hderr ⊢
      nlinarith
end CohnElkies

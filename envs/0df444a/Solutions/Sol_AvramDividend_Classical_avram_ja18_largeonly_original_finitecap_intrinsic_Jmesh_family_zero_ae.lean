-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_largeonly_original_finitecap_intrinsic_Jmesh_family_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:56:35.128274+00:00
-- url     : https://prove2.me/submissions/52dd31cd-900b-4840-b417-58fd20b25e7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every physical small-mark-only stopped gain family is trivial in a large-only jump model. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνsmall : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (σ : Ω → ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJmesh : ∀ k : ℕ, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WJ : ℕ → Ω → ℝ),
      ∀ ω : Ω, J k ω =
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, J k ω = 0 := by
  intro k
  obtain ⟨S, a, b, WJ, hmesh⟩ := hJmesh k
  have hz : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Jsmall u ω = 0 :=
    avram_b28_original_no_small_negative_jump_limit_zero
      X hνsmall hLarge Jsmall hJsource
  filter_upwards [hz] with ω hω
  simp [hmesh ω, hω]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_levy_single_contact_raw_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:11:07.065955+00:00
-- url     : https://prove2.me/submissions/9ff6fb0f-f862-488d-a4bd-1e75466bd188

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_single_contact_raw_residual_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Specialises the exact one-cell contact residual to the original
    bounded-variation Lévy drift, sample path, and intrinsic jump series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (W : ℕ → ℝ) (E : ℕ → Prop) (hmono : Monotone u)
    (hE : ∀ i, E i → u i < τ) :
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    let Raw := ∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0
    let Stopped := ∑ i ∈ Finset.range n,
      if E i then W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0
    ∃ t : ℝ, Raw = Stopped + t ∧
      (t = 0 ∨ ∃ i ∈ Finset.range n,
        E i ∧ τ < u (i + 1) ∧
          t = W i * (R τ - R (u (i + 1)))) := by
  exact avram_bv_strict12_original_single_contact_raw_residual_certificate
    n u τ
    (fun t => ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0))
    W E hmono hE

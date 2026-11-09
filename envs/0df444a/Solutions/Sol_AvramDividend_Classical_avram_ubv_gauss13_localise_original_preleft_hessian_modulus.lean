-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_hessian_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:25:36.509657+00:00
-- url     : https://prove2.me/submissions/edbc95de-a09b-4dcc-966c-82cd17b82a23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (ω : Ω) (t : ℝ≥0) (y : ℝ),
          let z := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          z ∈ Set.Icc a b →
          y ∈ Set.Icc a b →
          dist y z < δ →
          dist (iteratedDeriv 2 w y) (iteratedDeriv 2 w z) < ε := by
  let S : Set ℝ := {r : ℝ | 0 < r ∧ ENNReal.ofReal r < C}
  have hopen : IsOpen S := by
    have hpos : IsOpen {r : ℝ | 0 < r} := isOpen_Ioi
    have hcap : IsOpen {r : ℝ | ENNReal.ofReal r < C} :=
      isOpen_Iio.preimage ENNReal.continuous_ofReal
    exact hpos.inter hcap
  have hband : Set.Icc a b ⊆ S := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2) hbcap⟩
  have hdiff1 : ContDiffOn ℝ 1 (deriv w) S :=
    hw.deriv_of_isOpen hopen (by norm_num)
  have hw2 : ContinuousOn (deriv (deriv w)) (Set.Icc a b) :=
    (hdiff1.continuousOn_deriv_of_isOpen hopen (by norm_num)).mono hband
  have huc : UniformContinuousOn (deriv (deriv w)) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw2
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff).mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω t y
  dsimp only
  intro hz hy hclose
  let z : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  have hderiv : dist (deriv (deriv w) y) (deriv (deriv w) z) < ε :=
    hmod y hy z hz hclose
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hderiv

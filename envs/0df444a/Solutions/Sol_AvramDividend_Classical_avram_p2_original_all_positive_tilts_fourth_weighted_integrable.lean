-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_all_positive_tilts_fourth_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:23:38.460239+00:00
-- url     : https://prove2.me/submissions/63c88619-de83-4c15-a2c8-108dcd3832fc

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every positively tilted original fourth exponential-deficit test is
integrable by five exact source Laplace moments; suitable for finite measures. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Integrable (fun ω => Real.exp (ρ * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) P := by
  have h0 : Integrable (fun ω => Real.exp (ρ * X.X t ω)) P :=
    (X.laplace t ρ hρ).1
  have h1 : Integrable (fun ω => Real.exp ((ρ + 1) * X.X t ω)) P :=
    (X.laplace t (ρ + 1) (by linarith)).1
  have h2 : Integrable (fun ω => Real.exp ((ρ + 2) * X.X t ω)) P :=
    (X.laplace t (ρ + 2) (by linarith)).1
  have h3 : Integrable (fun ω => Real.exp ((ρ + 3) * X.X t ω)) P :=
    (X.laplace t (ρ + 3) (by linarith)).1
  have h4 : Integrable (fun ω => Real.exp ((ρ + 4) * X.X t ω)) P :=
    (X.laplace t (ρ + 4) (by linarith)).1
  have hsum : Integrable (fun ω =>
      Real.exp ((ρ + 4) * X.X t ω) -
      4 * Real.exp ((ρ + 3) * X.X t ω) +
      6 * Real.exp ((ρ + 2) * X.X t ω) -
      4 * Real.exp ((ρ + 1) * X.X t ω) +
      Real.exp (ρ * X.X t ω)) P :=
    ((((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
      (h1.const_mul 4)).add h0)
  have e1 (z : ℝ) :
      Real.exp ((ρ + 1) * z) = Real.exp (ρ * z) * Real.exp z := by
    rw [show (ρ + 1) * z = ρ * z + z by ring, Real.exp_add]
  have e2 (z : ℝ) :
      Real.exp ((ρ + 2) * z) = Real.exp (ρ * z) * (Real.exp z) ^ 2 := by
    rw [show (ρ + 2) * z = (ρ * z + z) + z by ring]
    simp only [Real.exp_add]
    ring
  have e3 (z : ℝ) :
      Real.exp ((ρ + 3) * z) = Real.exp (ρ * z) * (Real.exp z) ^ 3 := by
    rw [show (ρ + 3) * z = ((ρ * z + z) + z) + z by ring]
    simp only [Real.exp_add]
    ring
  have e4 (z : ℝ) :
      Real.exp ((ρ + 4) * z) = Real.exp (ρ * z) * (Real.exp z) ^ 4 := by
    rw [show (ρ + 4) * z = (((ρ * z + z) + z) + z) + z by ring]
    simp only [Real.exp_add]
    ring
  have hpoly (z : ℝ) :
      Real.exp (ρ * z) * (Real.exp z - 1) ^ 4 =
        Real.exp ((ρ + 4) * z) -
        4 * Real.exp ((ρ + 3) * z) +
        6 * Real.exp ((ρ + 2) * z) -
        4 * Real.exp ((ρ + 1) * z) +
        Real.exp (ρ * z) := by
    rw [e4 z, e3 z, e2 z, e1 z]
    ring
  have hfun : (fun ω : Ω => Real.exp (ρ * X.X t ω) *
      (Real.exp (X.X t ω) - 1) ^ 4) =
      (fun ω : Ω =>
        Real.exp ((ρ + 4) * X.X t ω) -
        4 * Real.exp ((ρ + 3) * X.X t ω) +
        6 * Real.exp ((ρ + 2) * X.X t ω) -
        4 * Real.exp ((ρ + 1) * X.X t ω) +
        Real.exp (ρ * X.X t ω)) := by
    funext ω
    exact hpoly (X.X t ω)
  rw [hfun]
  exact hsum

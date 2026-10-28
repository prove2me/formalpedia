-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_positive_root_finite_secant_and_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:47:09.02133+00:00
-- url     : https://prove2.me/submissions/b15b9814-bd5a-43e1-b37b-29c55de2ba61

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_esscher_convex_positive_shift_right_secant_limit
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_right_secant_derivative_lower
import Theorems.Thm_AvramDividend_Classical_esscher_levy_root_limit_and_right_secant_quotient
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The actual Levy exponent has a finite strictly positive right slope at
    every positive q-root, and its positive shifted roots have that slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    ∃ (m : ℝ) (root : ℝ → ℝ),
      q / phi ≤ m ∧ 0 < m ∧
      (∀ p : ℝ, 0 < p → 0 < root p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + root p) - q = p) ∧
      Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      Tendsto (fun p : ℝ => p / root p)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by
  let m : ℝ := derivWithin X.ψ (Ioi phi) phi
  have hconv : ConvexOn ℝ (Ici (0 : ℝ)) X.ψ :=
    levy_laplace_exponent_convexOn_nonnegative X
  have hsec : Tendsto
      (fun h : ℝ => (X.ψ (phi + h) - X.ψ phi) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) :=
    esscher_convex_positive_shift_right_secant_limit X.ψ phi hphi hconv
  obtain ⟨hlower, hmpos⟩ :=
    esscher_levy_positive_root_right_secant_derivative_lower
      X q phi m hq hphi hroot hsec
  obtain ⟨root, hpos, hlevel, hzero, hquot⟩ :=
    esscher_levy_root_limit_and_right_secant_quotient
      X q phi m hq hphi hroot hsec
  exact ⟨m, root, hlower, hmpos, hpos, hlevel, hzero, hquot⟩

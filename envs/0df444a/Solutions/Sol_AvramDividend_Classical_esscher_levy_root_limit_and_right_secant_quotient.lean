-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_root_limit_and_right_secant_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:46:12.213052+00:00
-- url     : https://prove2.me/submissions/5a64ec24-8e43-408d-9a75-d40b747ba825

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_family_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_esscher_right_secant_root_quotient_limit
open AvramDividend.Classical MeasureTheory Filter Set
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi m : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q)
    (hsec : Tendsto
      (fun h : ℝ => (X.ψ (phi + h) - X.ψ phi) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m)) :
    ∃ root : ℝ → ℝ,
      (∀ p : ℝ, 0 < p → 0 < root p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + root p) - q = p) ∧
      Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      Tendsto (fun p : ℝ => p / root p)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by
  obtain ⟨root, hpos, hr, hlim⟩ :=
    AvramDividend.Classical.esscher_levy_positive_root_family_tendsto_zero X q phi hq hphi hroot
  refine ⟨root, hpos, hr, hlim, ?_⟩
  exact AvramDividend.Classical.esscher_right_secant_root_quotient_limit X.ψ phi m root
    (fun p hp => by rw [hroot]; exact hr p hp) hlim hsec

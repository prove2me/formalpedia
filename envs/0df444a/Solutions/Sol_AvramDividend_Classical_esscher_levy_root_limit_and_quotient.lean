-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_root_limit_and_quotient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:18:01.697979+00:00
-- url     : https://prove2.me/submissions/e289afff-492d-44ad-b058-940273687991

import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_family_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_esscher_root_quotient_tendsto_of_hasDerivAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Full canonical Esscher root asymptotics conditional only on exponent differentiability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi m : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hderiv : HasDerivAt X.ψ m phi) :
    ∃ lambda : ℝ → ℝ,
      (∀ p : ℝ, 0 < p → 0 < lambda p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + lambda p) - q = p) ∧
      Tendsto lambda (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) ∧
      Tendsto (fun p : ℝ => p / lambda p)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by
  have hm : 0 < m :=
    (esscher_levy_positive_root_derivative_lower
      X q phi m hq hphi hroot hderiv).2
  obtain ⟨lambda, hpos, hfamily, hlimit⟩ :=
    esscher_levy_positive_root_family_tendsto_zero
      X q phi hq hphi hroot
  have hzero :
      (fun beta : ℝ => X.ψ (phi + beta) - q) 0 = 0 := by
    simp [hroot]
  have hraw :
      HasDerivAt (fun beta : ℝ => X.ψ (phi + beta)) m 0 :=
    HasDerivAt.comp_const_add phi 0 (by simpa only [add_zero] using hderiv)
  have hshift :
      HasDerivAt (fun beta : ℝ => X.ψ (phi + beta) - q) m 0 :=
    hraw.sub_const q
  have hquotient := esscher_root_quotient_tendsto_of_hasDerivAt
    (fun beta : ℝ => X.ψ (phi + beta) - q)
    lambda m hzero hm hshift hlimit hfamily
  exact ⟨lambda, hpos, hfamily, hlimit, hquotient⟩

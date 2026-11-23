-- Prove2me | solution 1 for Deduction.landau_pole_re_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:20.115716+00:00
-- url     : https://prove2.me/submissions/c95fdd44-2749-4020-a38a-796f0b14f623

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauPoleReLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {σ : ℝ}
    (hσ : 2 < σ) : ∃ M : ℝ, ∀ s : ℂ, σ ≤ s.re → ‖Φ s‖ ≤ M := by
  obtain ⟨C, hC⟩ := hP.growth
  refine ⟨∫ u in Ioi (0 : ℝ), C * Real.exp (-(σ - 2) * u), fun s hs => ?_⟩
  rw [hP.laplace s (lt_of_lt_of_le hσ hs)]
  refine norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hσ)).const_mul C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have h1 := hC u hu0
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have h2 : Real.exp (-s.re * u) ≤ Real.exp (-σ * u) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc |g u| * Real.exp (-s.re * u) ≤ (C * Real.exp (2 * u)) * Real.exp (-σ * u) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le ((abs_nonneg _).trans h1)
    _ = C * Real.exp (-(σ - 2) * u) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
end Deduction

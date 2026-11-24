-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.tau_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:32.949462+00:00
-- url     : https://prove2.me/submissions/af11b1e8-bd87-431d-94cb-c4f1bb0f0d39

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TauIntegral := by
  intro f j n0 hf hj hn
  have hpos : 1 ≤ j * n0 * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, 2 * j * n0 * f = (M + 1) + 1 := ⟨2 * (j * n0 * f) - 2, by
    have : 2 * j * n0 * f = 2 * (j * n0 * f) := by ring
    omega⟩
  have e : ∀ t : ℝ, t ^ (2 * j * n0 * f) * (2 * (f:ℝ) * j / t) = 2 * (f:ℝ) * j * t ^ (M + 1) := by
    intro t
    rw [hM]
    by_cases ht : t = 0
    · subst ht; simp
    · field_simp
      ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hMr : ((M + 1 : ℕ) : ℝ) + 1 = 2 * j * n0 * f := by exact_mod_cast hM.symm
  rw [hM, hMr]
  have : (0:ℝ) < j := by exact_mod_cast hj
  have : (0:ℝ) < f := by exact_mod_cast hf
  have : (0:ℝ) < n0 := by exact_mod_cast hn
  field_simp
  simp
end Formalism.HermitianLatticeCounting.P

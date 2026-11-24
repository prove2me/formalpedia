-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ratio_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:18.93767+00:00
-- url     : https://prove2.me/submissions/f394e37b-f48e-4d1c-9998-2bf714e187f5

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_sum_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.RatioSum := by
  intro C k f g Hh hg hH hρ
  set ρ := ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ s ∈ Finset.Icc 1 (k - 1),
      ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ (1 / 2 : ℝ) ^ s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hsk : s ≤ k := by omega
    have hc : ((C * s * f : ℕ) : ℝ) ≤ ((C * k * f : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsk)
    calc ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f)
        ≤ ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * k * f : ℕ) : ℝ) ^ (4 * s * f) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hc _
      _ = ρ ^ s := by
          rw [hρd, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          have e1 : s * k * f = k * f * s := by ring
          have e2 : 4 * s * f = 4 * f * s := by ring
          rw [e1, e2]
      _ ≤ (1 / 2 : ℝ) ^ s := pow_le_pow_left₀ hρ0 hρ _
  calc _ ≤ ∑ s ∈ Finset.Icc 1 (k - 1), (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hterm
    _ = 1 - (1 / 2) ^ (k - 1) := sum_half _
    _ ≤ 1 := by have : (0 : ℝ) ≤ (1 / 2) ^ (k - 1) := by positivity
                linarith
end Formalism.HermitianLatticeCounting.P

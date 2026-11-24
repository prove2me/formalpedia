-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.factorialValuationLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.045623+00:00
-- url     : https://prove2.me/submissions/2db33b51-9279-429b-8250-d5309ce1d19d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_digits_sum_le_lgN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : FactorialLg := by
  intro p m hp
  have : Fact p.Prime := ⟨hp⟩
  have h1 := sub_one_mul_padicValNat_factorial (p := p) m
  have h2 := Nat.digit_sum_le p m
  have h3 := digits_sum_le_lgN p m hp.one_lt
  have h4 : m ≤ (p - 1) * (padicValNat p m.factorial + lgN p m) := by
    rw [mul_add, h1]
    omega
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have h5 : (m : ℝ) ≤ ((p : ℝ) - 1) * ((padicValNat p m.factorial : ℝ) + lgN p m) := by
    have h6 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [← h6]
    exact_mod_cast h4
  rw [sub_le_iff_le_add, div_le_iff₀ hp1]
  linarith
end Formalism.InvariantFactorPaths.G7

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.not_dvd_choose_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:19.646438+00:00
-- url     : https://prove2.me/submissions/72920083-abc6-459c-9941-ea7f8d5a70c7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ k * m).choose (p ^ k) := by
  have := Fact.mk hp
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    intro h
    apply ih
    have key := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p ^ (k + 1) * m)
      (k := p ^ (k + 1))
    have e1 : p ^ (k + 1) * m % p = 0 := by
      rw [pow_succ', mul_assoc]; exact Nat.mul_mod_right _ _
    have e2 : p ^ (k + 1) % p = 0 := by
      rw [pow_succ']; exact Nat.mul_mod_right _ _
    have e3 : p ^ (k + 1) * m / p = p ^ k * m := by
      rw [pow_succ', mul_assoc]; exact Nat.mul_div_cancel_left _ hp.pos
    have e4 : p ^ (k + 1) / p = p ^ k := by
      rw [pow_succ']; exact Nat.mul_div_cancel_left _ hp.pos
    rw [e1, e2, e3, e4, Nat.choose_self, one_mul] at key
    exact (key.dvd_iff dvd_rfl).1 h
end Formalism.InvariantFactorPaths.G7.LemOne

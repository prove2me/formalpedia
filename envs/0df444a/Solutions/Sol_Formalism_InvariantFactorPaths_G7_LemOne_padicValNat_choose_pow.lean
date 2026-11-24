-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.padicValNat_choose_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:19.913578+00:00
-- url     : https://prove2.me/submissions/62aa486d-5c01-4abe-8601-33a8fbe8e376

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (k : ℕ) :
    padicValNat p ((p ^ (k + 1)).choose (p ^ k)) = 1 := by
  have := Fact.mk hp
  have hle : p ^ k ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
  have h := hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_pos hp.pos k).ne'
  have hc : (p ^ (k + 1)).choose (p ^ k) ≠ 0 := (Nat.choose_pos hle).ne'
  rw [← padicValNat_eq_emultiplicity hc, ← padicValNat_eq_emultiplicity (pow_pos hp.pos k).ne',
    padicValNat.prime_pow] at h
  have h' : padicValNat p ((p ^ (k + 1)).choose (p ^ k)) + k = k + 1 := by exact_mod_cast h
  omega
end Formalism.InvariantFactorPaths.G7.LemOne

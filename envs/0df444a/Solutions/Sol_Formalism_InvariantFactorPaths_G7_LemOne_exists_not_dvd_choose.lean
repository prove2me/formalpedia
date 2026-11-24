-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.exists_not_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.781342+00:00
-- url     : https://prove2.me/submissions/f0808ad1-2cdc-4cea-a259-425a7f255369

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_not_dvd_choose_pow_mul

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n)
    (hpow : ∀ k, n ≠ p ^ k) : ∃ i, 0 < i ∧ i < n ∧ ¬ p ∣ n.choose i := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  refine ⟨p ^ k, pow_pos hp.pos k, ?_, not_dvd_choose_pow_mul hp k m hm⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : m ≠ 1 := by rintro rfl; exact hpow k (by simp)
  have : 2 ≤ m := by omega
  have hpos := pow_pos hp.pos k
  nlinarith
end Formalism.InvariantFactorPaths.G7.LemOne

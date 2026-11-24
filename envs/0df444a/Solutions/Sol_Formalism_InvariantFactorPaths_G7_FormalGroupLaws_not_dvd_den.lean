-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.not_dvd_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:58.522919+00:00
-- url     : https://prove2.me/submissions/3f2d07d6-f3b6-4d2f-b3d6-5aadb86b779f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul
import Theorems.Thm_Formalism_LT_LTL_Cong_mul
import Theorems.Thm_Formalism_LT_LTL_Near_mul


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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution {p : ℕ} [Fact p.Prime] (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) : ¬ p ∣ r.den := by
  intro hd
  have hp := Fact.out (p := p.Prime)
  rw [Padic.eq_padicNorm] at h
  have hden : padicNorm p ((r.den : ℤ) : ℚ) < 1 :=
    (padicNorm.int_lt_one_iff _).mpr (by exact_mod_cast hd)
  have hnum : padicNorm p ((r.num : ℤ) : ℚ) < 1 := by
    have hc : ((r.num : ℤ) : ℚ) = r * ((r.den : ℤ) : ℚ) := by
      push_cast
      exact (Rat.mul_den_eq_num r).symm
    rw [hc, padicNorm.mul]
    calc padicNorm p r * padicNorm p ((r.den : ℤ) : ℚ) ≤ 1 * padicNorm p ((r.den : ℤ) : ℚ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h) (padicNorm.nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have h1 : (p : ℤ) ∣ r.num := (padicNorm.int_lt_one_iff _).mp hnum
  have h2 : p ∣ r.num.natAbs := Int.natCast_dvd.mp h1
  have h3 := Nat.dvd_gcd h2 hd
  rw [Nat.Coprime.gcd_eq_one r.reduced] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws

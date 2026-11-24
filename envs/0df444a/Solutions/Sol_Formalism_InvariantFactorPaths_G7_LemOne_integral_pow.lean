-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.integral_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:56.506585+00:00
-- url     : https://prove2.me/submissions/d5f27e75-0cbc-4db7-ad25-71f503df5c3b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_integral_mul

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
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι K} (hf : Integral f) (d : ℕ) :
    Integral (f ^ d) := by
  classical
  induction d with
  | zero =>
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ d ih => rw [pow_succ]; exact integral_mul ih hf
end Formalism.InvariantFactorPaths.G7.LemOne

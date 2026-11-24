-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.coeff_pow_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:54.546939+00:00
-- url     : https://prove2.me/submissions/35b7c506-6d12-4c72-a1bf-896962763abc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_order_pow_sub_lin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_degree_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_coeff_lin_pow

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
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) (n i : ℕ) (hi : i ≤ n) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i))
      (F ^ n) = (n.choose i : K) := by
  rw [← coeff_lin_pow (K := K) n i hi, ← sub_eq_zero, ← map_sub]
  refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_pow_sub_lin hF0 hF1 n))
  rw [degree_pair]
  have : i + (n - i) = n := by omega
  rw [this]
  exact_mod_cast Nat.lt_succ_self n
end Formalism.InvariantFactorPaths.G7.LemOne

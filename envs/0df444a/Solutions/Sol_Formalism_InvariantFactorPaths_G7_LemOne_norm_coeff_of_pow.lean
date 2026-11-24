-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:20.567474+00:00
-- url     : https://prove2.me/submissions/490d59c9-df0a-4add-b563-de789fadd2e9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_padicValNat_choose_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_mul_choose
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_p_lt_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) (k : ℕ)
    (hlow : ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1) :
    ‖(p : K) * PowerSeries.coeff (p ^ (k + 1)) h‖ ≤ 1 := by
  have hlt : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)
  have := norm_coeff_mul_choose hF0 hFi hF1 hcob hlow (pow_pos hp.pos k) hlt
  rwa [norm_mul, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp (norm_p_lt_one hp hnp)
    (Nat.choose_pos hlt.le).ne', padicValNat_choose_pow hp k, pow_one, mul_comm, ← norm_mul] at this
end Formalism.InvariantFactorPaths.G7.LemOne

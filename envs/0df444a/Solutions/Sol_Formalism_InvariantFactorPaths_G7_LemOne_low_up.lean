-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.low_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:13.277395+00:00
-- url     : https://prove2.me/submissions/2ed5a462-a818-41ca-af82-9ed54fae8b28

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_of_not_pow

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
    (hlow : ∀ d ≤ p ^ k, ‖PowerSeries.coeff d h‖ ≤ 1) :
    ∀ d < p ^ (k + 1), ‖PowerSeries.coeff d h‖ ≤ 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    by_cases hdk : d ≤ p ^ k
    · exact hlow d hdk
    · have hk1 : 1 ≤ p ^ k := pow_pos hp.pos k
      refine norm_coeff_of_not_pow hp hnp hF0 hFi hF1 hcob (by omega) ?_
        fun d' hd' => ih d' hd' (lt_trans hd' hd)
      rintro m rfl
      have h1 : k < m := (Nat.pow_lt_pow_iff_right hp.one_lt).1 (not_le.1 hdk)
      have h2 : m < k + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
      omega
end Formalism.InvariantFactorPaths.G7.LemOne

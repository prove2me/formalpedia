-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_lin_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:50.029984+00:00
-- url     : https://prove2.me/submissions/f30014f9-0269-4baa-aab4-d256f79ce302

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob2_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_linW
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {w : ZMod (2 * ν) → K} (hw1 : ∀ s, ‖w s‖ ≤ 1)
    (hw2 : ∀ s, ‖w (s + 2) - w s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹) (ab : Fin r0 × Fin r1) (l : ℕ) :
    Cg p (linW w ab ^ ((p ^ 2) ^ l))
      (∑ s : ZMod (2 * ν), MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
        (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := by
  induction l with
  | zero => simpa [linW] using cg_refl p _
  | succ l ih =>
    have hI : ∀ s ∈ (Finset.univ : Finset (ZMod (2 * ν))),
        Integral (MvPowerSeries.C (w (s + 2 * (l : ZMod (2 * ν)))) *
          (MvPowerSeries.X (s, ab) : MvPowerSeries (ZV ν r0 r1) K) ^ ((p ^ 2) ^ l)) := fun s _ =>
      integral_mul (integral_C (hw1 _)) (integral_pow (integral_X _) _)
    rw [pow_succ, pow_mul]
    refine cg_trans (cg_pow (integral_pow (integral_linW hw1 ab) _) (integral_sum _ _ hI) ih
      (p ^ 2)) ?_
    refine cg_trans (cg_frob2_sum hp hn _ _ hI) ?_
    refine cg_sum _ _ _ fun s _ => ?_
    rw [mul_pow, ← pow_mul, ← map_pow]
    refine cg_mul (integral_C ?_) (integral_pow (integral_X _) _) (cg_C ?_) (cg_refl _ _)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hw1 _)
    · have := hw2 (s + 2 * (l : ZMod (2 * ν)))
      have e : s + 2 * ((l + 1 : ℕ) : ZMod (2 * ν)) = s + 2 * (l : ZMod (2 * ν)) + 2 := by
        push_cast; ring
      rw [norm_sub_rev, e]
      exact this
end Formalism.InvariantFactorPaths.G7.TwoS

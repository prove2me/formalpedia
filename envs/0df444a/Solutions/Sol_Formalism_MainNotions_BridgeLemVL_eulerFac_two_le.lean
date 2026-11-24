-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVL.eulerFac_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:38:59.367799+00:00
-- url     : https://prove2.me/submissions/78313822-4839-4751-856f-744f41fd3bc8

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_abs_smallTerm_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_eulerFac_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_prime
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_inv_one_sub_le_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVL
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.eulerFac K 2 P ≤ Real.exp (2 * ((resChar P : ℝ) ^ 2)⁻¹) := by
  have hu := abs_smallTerm_le hK hP (le_refl 2)
  have hp : (2 : ℝ) ≤ (resChar P : ℝ) := by exact_mod_cast (resChar_prime hP).two_le
  have hq : ((resChar P : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  set u := smallTerm 2 P with hudef
  set y := ((resChar P : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hua : |u| ≤ 1 / 2 := by linarith
  have hpos : 0 < 1 + u := by linarith [neg_abs_le u]
  have key : (1 + u)⁻¹ ≤ Real.exp (2 * y) := by
    have h1 : 0 < 1 - |u| := by linarith
    have h2 : (1 + u)⁻¹ ≤ (1 - |u|)⁻¹ := by
      apply inv_anti₀ h1
      linarith [neg_abs_le u]
    exact h2.trans ((Formalism.MainNotions.MassRatioZetaBound.inv_one_sub_le_exp (abs_nonneg u) hua).trans
      (Real.exp_le_exp.2 (by linarith)))
  rw [eulerFac_eq]
  split_ifs with hc
  · exact key
  · rcases le_or_gt 1 (1 + u) with h | h
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)
        _ ≤ Real.exp (2 * y) := Real.one_le_exp (by positivity)
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ (1 + u) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hpos h.le (by norm_num)
        _ = (1 + u)⁻¹ := Real.rpow_neg_one _
        _ ≤ Real.exp (2 * y) := key
end Formalism.MainNotions.BridgeLemVL

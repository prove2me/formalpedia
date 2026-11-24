-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_le_pow_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:59.151525+00:00
-- url     : https://prove2.me/submissions/4c7a6e4c-2f6a-41ec-aefe-6b2006edd213

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_zeta_three_halves_nonneg
import Theorems.Thm_Formalism_MainNotions_MassRatioBoundPower_exp_le_two_pow
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_mass_ratio_rhs_le_factorial
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_one_le_two_vInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioBoundPower
theorem _root_.solution [StarRing K] (hd : Module.finrank ℚ K ≤ 2 * Formalism.HermitianLatticesTheory.fDeg K) {n M : ℕ} (h3 : 3 ≤ M) (hMn : M ≤ n)
    {Y : ℝ} (hY : 2 ≤ Y) (hn : (n : ℝ) ≤ Y) (hv : 2 * Formalism.HermitianLatticesTheory.vInv K ≤ Y) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤ Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K) := by
  refine (mass_ratio_rhs_le_factorial h3).trans ?_
  set f := Formalism.HermitianLatticesTheory.fDeg K with hf
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hv0 : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by have := one_le_two_vInv (K := K); linarith
  have hfac : (((M - 1).factorial : ℕ) : ℝ) ≤ Y ^ n := by
    have h1 : (M - 1).factorial ≤ (M - 1) ^ (M - 1) := Nat.factorial_le_pow (M - 1)
    have h2 : ((M - 1 : ℕ) : ℝ) ≤ Y := by
      have : ((M - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le M 1).trans hMn
      linarith
    calc (((M - 1).factorial : ℕ) : ℝ) ≤ (((M - 1) ^ (M - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((M - 1 : ℕ) : ℝ) ^ (M - 1) := by push_cast; ring
      _ ≤ Y ^ (M - 1) := pow_le_pow_left₀ (by positivity) h2 _
      _ ≤ Y ^ n := pow_le_pow_right₀ hY1 (by omega)
  have hvp : Formalism.HermitianLatticesTheory.vInv K / Real.pi ≤ Y := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc Formalism.HermitianLatticesTheory.vInv K / Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K := div_le_self hv0 hpi
      _ ≤ Y := by linarith
  have hpow : (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M ≤ Y ^ n :=
    (pow_le_pow_left₀ (by positivity) hvp M).trans (pow_le_pow_right₀ hY1 (by omega))
  have hA : ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ f ≤ (Y ^ n * Y ^ n) ^ f :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul hfac hpow (by positivity) (by positivity)) f
  have hB : Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ (Y ^ cZ) ^ f := by
    have hd' : (Module.finrank ℚ K : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hd
    calc Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ Real.exp ((f : ℝ) * (4 * zetaGL3GL2)) := by
          apply Real.exp_le_exp.2; nlinarith [zeta_three_halves_nonneg]
      _ = Real.exp (4 * zetaGL3GL2) ^ f := Real.exp_nat_mul _ _
      _ ≤ ((2 : ℝ) ^ cZ) ^ f := pow_le_pow_left₀ (Real.exp_pos _).le exp_le_two_pow f
      _ ≤ (Y ^ cZ) ^ f := pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hY _) f
  calc ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ f *
        Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ (Y ^ n * Y ^ n) ^ f * (Y ^ cZ) ^ f :=
        mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = Y ^ ((2 * n + cZ) * f) := by
        rw [← pow_add, ← mul_pow, ← pow_add, ← pow_mul]; congr 1; ring
end Formalism.MainNotions.MassRatioBoundPower

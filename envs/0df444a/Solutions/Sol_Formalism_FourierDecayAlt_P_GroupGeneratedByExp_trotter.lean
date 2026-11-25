-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:49.501028+00:00
-- url     : https://prove2.me/submissions/b080983f-0aa9-4919-ae8f-5455a9430f53

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_norm_exp_mul_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_norm_pow_sub_pow_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_diff_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  set F : ℝ → 𝔸 := fun t : ℝ =>
    NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y)) with hF
  have hF0 : F 0 = 0 := by simp [hF, NormedSpace.exp_zero]
  have hsl := (diff_hasDerivAt X Y).tendsto_slope_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (inv_pos.2 this).ne'
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) • F ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := hsl.comp hinv
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, inv_inv]
    rw [show NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp ((0 : ℝ) • Y) - NormedSpace.exp ((0 : ℝ) • (X + Y)) = 0
      from hF0, sub_zero]
  have h2 : Tendsto (fun n : ℕ => Real.exp s * ‖(1 : 𝔸)‖ * ‖(n : ℝ) • F ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
    have := (h1.norm).const_mul (Real.exp s * ‖(1 : 𝔸)‖)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := (inv_pos.2 hn0).le
  have hb : NormedSpace.exp (X + Y) = NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) ^ n := by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hq : (1 : ℝ) ≤ Real.exp ((n : ℝ)⁻¹ * s) := Real.one_le_exp (by positivity)
  have ha : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    rw [mul_assoc]
    refine (norm_exp_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_exp_mul_le _ _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hni, hs, mul_add]
  have hb' : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) * u‖ ≤ Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    refine (norm_exp_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hni
  rw [hb]
  refine (norm_pow_sub_pow_le hq ha hb' n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, show (n : ℝ) * ((n : ℝ)⁻¹ * s) = s by field_simp, norm_smul, Real.norm_of_nonneg hn0.le]
  ring
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp

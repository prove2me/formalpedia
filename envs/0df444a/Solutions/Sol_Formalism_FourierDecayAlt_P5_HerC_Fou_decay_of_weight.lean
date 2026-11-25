-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.decay_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:18.030541+00:00
-- url     : https://prove2.me/submissions/d40045e8-a7f7-4830-8b49-192a113a7839

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_au_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_contDiff_u
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_norm_iteratedFDeriv_w_le
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_inv_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ ∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hEb 0 (Nat.zero_le _) 0)
  have hDw : D = fun x => ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) • E x := by
    funext x
    rw [hDE x, smul_smul]
    have hq : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    field_simp
    simp
  have hwc : ContDiff ℝ m (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) :=
    (contDiff_u m).mul (contDiff_u m)
  refine ⟨hDw ▸ hwc.smul hE, ?_⟩
  set Kw : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * au l * au (i - l) with hKw
  have hKw0 : ∀ i, 0 ≤ Kw i := fun i =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (au_nonneg _)) (au_nonneg _)
  set Cn : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Kw i * B with hCn
  have hCn0 : ∀ n, 0 ≤ Cn n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hKw0 i)) hB
  refine ⟨4 * ∑ n ∈ Finset.range (m + 1), Cn n, fun j hj x => ?_⟩
  have hq0 : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  have hstep : ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
    rw [hDw]
    refine (norm_iteratedFDeriv_smul_le (N := (j : ℕ∞)) (hwc.of_le (by exact_mod_cast hj))
      (hE.of_le (by exact_mod_cast hj)) x le_rfl).trans ?_
    rw [hCn, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ *
          ‖iteratedFDeriv ℝ (j - i) E x‖
        ≤ (j.choose i : ℝ) * (Kw i * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹)) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_w_le i x) (Nat.cast_nonneg _))
            (hEb (j - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKw0 i) hq0))
      _ = (j.choose i : ℝ) * Kw i * B * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring
  have hsum : Cn j ≤ ∑ n ∈ Finset.range (m + 1), Cn n :=
    Finset.single_le_sum (fun n _ => hCn0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := hstep
    _ ≤ (∑ n ∈ Finset.range (m + 1), Cn n) * (4 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
        mul_le_mul hsum (inv_sq_le x) hq0 (Finset.sum_nonneg fun n _ => hCn0 n)
    _ = 4 * (∑ n ∈ Finset.range (m + 1), Cn n) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by ring
end Formalism.FourierDecayAlt.P5.HerC.Fou

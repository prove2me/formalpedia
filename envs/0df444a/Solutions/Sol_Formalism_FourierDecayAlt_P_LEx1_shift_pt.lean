-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.shift_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:09.662978+00:00
-- url     : https://prove2.me/submissions/5388cac3-c997-4294-ad30-a707e10918d1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_norm_add_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution {B : Base} (S : Step B) (CR Cd : ℝ) (hCR : 0 ≤ CR) (hCd : 0 ≤ Cd) (hW : S.WPos) (h5 : S.ShiftFormula)
    (hRes : S.Residues CR) (hWR : S.WeightRatio Cd) (Y s : ℝ) (hY : Y ∈ S.J) (hYs : Y + s ∈ S.J) (ω : B.Ω) :
    LE.sq B (S.d Y) (S.gs Y s) ω ≤ (1 + CR) ^ 2 * (Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) := by
  set u1 : S.ι → ℂ := fun i => S.gX (Y + s) ω (false, i) with hu1
  set u2 : S.ι → ℂ := fun i => S.gX (Y + s) ω (true, i) with hu2
  set t : S.ι → ℂ := fun i => ∑ j, (S.ee Y ω i j - S.ee (Y + s) ω i j) * u1 j with ht
  set A := ∑ i, S.d Y ω (false, i) * ‖u1 i‖ ^ 2 with hA
  set Bq := ∑ i, S.d Y ω (true, i) * ‖u2 i‖ ^ 2 with hBq
  set Tq := ∑ i, S.d Y ω (true, i) * ‖t i‖ ^ 2 with hTq
  set V := ∑ i, S.d Y ω (true, i) * ‖u2 i + t i‖ ^ 2 with hV
  have hd : ∀ k, 0 ≤ S.d Y ω k := fun k => (hW.2 Y hY ω k).le
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hT : Tq ≤ CR ^ 2 * A := hRes Y s hY hYs ω u1
  have hL : LE.sq B (S.d Y) (S.gs Y s) ω = V + A := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).2]
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).1]
  have hR : Bq + A ≤ Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool, mul_add, Finset.mul_sum, Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
  have hVb : CR * V ≤ CR * (1 + CR) * Bq + (1 + CR) * Tq := by
    rw [hV, hBq, hTq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have := mul_le_mul_of_nonneg_left (norm_add_sq_le (u2 i) (t i) CR hCR) (hd (true, i))
    nlinarith
  have key : V + A ≤ (1 + CR) ^ 2 * (Bq + A) := by
    rcases hCR.eq_or_lt with h0 | hpos
    · have hT0 : Tq ≤ 0 := by rw [← h0] at hT; simpa using hT
      have hz : ∀ i ∈ (Finset.univ : Finset S.ι), S.d Y ω (true, i) * ‖t i‖ ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))).1
        exact le_antisymm hT0 (Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity)))
      have hVB : V = Bq := by
        apply Finset.sum_congr rfl; intro i hi
        have h1 := hz i hi
        have h2 : t i = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · exact absurd h (hW.2 Y hY ω _).ne'
          · simpa using h
        rw [h2, add_zero]
      rw [hVB, ← h0]; simp
    · have : CR * V ≤ CR * ((1 + CR) * Bq + (1 + CR) * CR * A) := by nlinarith
      have hV2 : V ≤ (1 + CR) * Bq + (1 + CR) * CR * A := le_of_mul_le_mul_left this hpos
      nlinarith
  rw [hL]
  exact le_trans key (mul_le_mul_of_nonneg_left hR (by positivity))
end Formalism.FourierDecayAlt.P.LEx1

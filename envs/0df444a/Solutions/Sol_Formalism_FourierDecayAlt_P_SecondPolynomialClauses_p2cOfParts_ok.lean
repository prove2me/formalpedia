-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p2cOfParts_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:00.377135+00:00
-- url     : https://prove2.me/submissions/7d69c0cc-8470-4ece-8d9e-da30b115ee42

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_cg_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_co_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution : LowerBlockNormalisedBoundFromComponents := by
  intro K d grid q nn w o W0 RL RV wt wt' bw Qw BB hinj hpos hQ hnn hBB hwt hwt' hbw hR H
  have hQw : K = 0 ∨ 0 ≤ Qw := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · exact Or.inl hK
    · right
      have h1 := hQ ⟨0, hK⟩ 0
      have h2 := (hpos ⟨0, hK⟩ 0).1
      have h3 := (hpos ⟨0, hK⟩ 0).2.1
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_neg_of_neg_of_pos hneg h3]
  have hZ2 : (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K = Qw ^ K * (BB ^ 2) ^ K := by
    rcases hQw with hK | hQ0
    · subst hK; simp
    · rw [← mul_pow, ← mul_pow]
      congr 1
      linear_combination (BB ^ 2) * Real.mul_self_sqrt hQ0
  have hN : ∀ j, nnProd nn 0 grid j * nnProd nn 1 grid j ≤ Qw ^ K * (BB ^ 2) ^ K * qProd q w grid j := by
    intro j
    unfold nnProd qProd
    rw [← Finset.prod_mul_distrib]
    have e : Qw ^ K * (BB ^ 2) ^ K * ∏ a, F7.qW q w (grid a (j a)) =
        ∏ a, (Qw * BB ^ 2 * F7.qW q w (grid a (j a))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [e]
    refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => ?_)
    · rw [add_zero]; exact mul_nonneg (hpos a (j a)).2.2.1.le (hpos a (j a)).2.2.2.le
    · rw [add_zero]
      have h1 := (div_le_iff₀ (hpos a (j a)).1).mp (hnn a (j a))
      have h2 := hQ a (j a)
      nlinarith [mul_nonneg (sq_nonneg BB) (sub_nonneg.mpr h2)]
  have hj : ∀ j, wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j) ≤
      (Real.sqrt Qw * BB) ^ K * ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) +
        wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2) := by
    intro j
    have hq0 : 0 < qProd q w grid j := Finset.prod_pos fun a _ => (hpos a (j a)).2.1
    have hN0 : 0 < nnProd nn 0 grid j := Finset.prod_pos fun a _ => by
      rw [add_zero]; exact (hpos a (j a)).2.2.1
    have hN1 : 0 < nnProd nn 1 grid j := Finset.prod_pos fun a _ => (hpos a (j a)).2.2.2
    have hX : 0 ≤ wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (hR j).1) (mul_pos hbw hN0).le
    have hY : 0 ≤ wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (hR j).2) (mul_pos hbw hN1).le
    have hZ : 0 ≤ (Real.sqrt Qw * BB) ^ K := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hBB) K
    have hc : 0 ≤ wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hR j).1) (hR j).2)
        (sq_nonneg _)
    have hL0 : 0 ≤ wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j) :=
      mul_nonneg (div_nonneg (mul_nonneg hwt hwt') hbw.le) (Real.sqrt_nonneg _)
    have e1 : (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) ^ 2 =
        (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) * (1 / qProd q w grid j) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (hR j).1 (hR j).2) hq0.le)]; ring
    have h3 : 1 / qProd q w grid j ≤ Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j) := by
      rw [div_le_div_iff₀ hq0 (mul_pos hN0 hN1)]; linarith [hN j]
    have e2 : (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
        (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) * (wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))) =
        (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) *
          (Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j)) := by
      rw [hZ2]; ring
    apply (pow_le_pow_iff_left₀ hL0 (mul_nonneg hZ (by linarith)) two_ne_zero).mp
    calc (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) ^ 2
        = (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) * (1 / qProd q w grid j) := e1
      _ ≤ (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) *
          (Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
          (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) * (wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))) := e2.symm
      _ ≤ (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) -
            wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))]) (mul_nonneg hZ hZ)
      _ = _ := by ring
  have hk : 0 ≤ wt * wt' / bw := div_nonneg (mul_nonneg hwt hwt') hbw.le
  have hcg0 : 0 ≤ ∏ a, cg grid a := Finset.prod_nonneg fun a _ => (cg_pos grid hinj a).le
  have hth : ∀ j, 0 ≤ F7.thGrid grid j := fun j =>
    Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  calc ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) = wt * wt' / bw * (‖o‖ ^ K * ‖W0‖) := by ring
    _ ≤ wt * wt' / bw * ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) :=
        mul_le_mul_of_nonneg_left H hk
    _ = (∏ a, cg grid a) * ∑ j, F7.thGrid grid j *
          (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [co_eq grid hinj j]; ring
    _ ≤ (∏ a, cg grid a) * ∑ j, F7.thGrid grid j * ((Real.sqrt Qw * BB) ^ K *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hth j)) hcg0
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.borderFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:45:01.915325+00:00
-- url     : https://prove2.me/submissions/31726b21-fc47-4872-b6c0-6fc885646f49

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_bS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_succAbove_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sgn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Tm_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expFCS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expLCS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expLCE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_dropS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_borderE_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Tm_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_rowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_snocCast_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hFC : ExpFirstCol) (hLC : ExpLastCol) (hFR : ExpFirstRow) (hLR : ExpLastRow)
    (hSk : QSkewRow) : BorderFull := by
  intro A _ _ n m E e es v hE hB u
  have hBE := borderE_of hFC hLR hSk A n m E e es v hE hB u
  obtain ⟨hinj, hee, hve, hvs⟩ := id hB
  have r0 : bS (bE e v) es ∘ (Fin.castSucc 0).succAbove = bS v es := by
    rw [← bE_bS, Fin.castSucc_zero, bE_succAbove_zero]
  have rW : ∀ w : Fin m, bS (bE e v) es ∘ w.succ.castSucc.succAbove =
      bE e (bS v es) ∘ w.castSucc.succ.succAbove := by
    intro w; rw [← bE_bS, Fin.succ_castSucc]
  have e1 : u - ((m + 1 : ℕ) : ℂ) = u - (m : ℂ) - 1 := by push_cast; ring
  simp only [snocCast_eq]
  rw [bE_bS, expLCS E hLC, Fin.sum_univ_succ, r0, e1]
  simp only [rW, bE_zero, bE_succ, Fin.val_zero, Fin.val_succ]
  rw [Tm_ne E _ hee]
  simp only [Tm_ne E _ (hvs _)]
  set C := qminor E v v (u - 1) with hC
  set Tee := Tm E u e e with hTee
  set Tss := Tm E (u - (m : ℂ) - 1) es es with hTss
  set Z : A := ∑ w : Fin m, ((-1 : ℤ) ^ (w : ℕ)) •
    (E es e * qminor E (bE e v ∘ w.succ.succAbove) v (u - 1) * E (v w) es) with hZ
  have L1 : ((-1 : ℤ) ^ (m + 1 + 0)) • (qminor E (bS v es) (bE e v) u * E e es) =
      (∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (bS v es ∘ w.castSucc.succAbove) v (u - 1) * E e es)) -
        E es e * C * E e es := by
    rw [expFCS E hFC, add_mul, smul_add, Finset.sum_mul, Finset.smul_sum, Tm_ne E _ hee.symm, smul_mul_assoc,
      smul_smul, ← pow_add, sgn_congr (a := m + 1 + 0 + m) (b := 1) (by omega), pow_one, neg_one_smul, ← sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Tm_ne E _ (hve w), smul_mul_assoc, smul_smul, ← pow_add, ← zsmul_eq_mul,
      sgn_congr (b := (w : ℕ) + 1 + m) (by omega)]
  have L3 : qminor E (bE e v) (bE e v) u * Tss = Tee * C * Tss -
      (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tss * E e (v x))) := by
    rw [hBE, sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_assoc, mul_assoc _ (E e (v x)) Tss, ← Tm_comm E hE _ hee.symm (hvs x), ← mul_assoc _ Tss]
  have R5 : (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1)) =
      -(E es e * C * E e es) + Z := by
    rw [expLCE E hLC, Tm_ne E _ hee, mul_add, mul_add, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
      sgn_congr (a := m + 1 + m) (b := 1) (by omega), pow_one, neg_one_smul, mul_assoc]
    congr 1
    rw [Finset.mul_sum, ← zsmul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Tm_ne E _ (hvs w), mul_smul_comm, smul_smul, ← pow_add, sgn_congr (b := (w : ℕ)) (by omega), mul_assoc]
  have L2 : (∑ w : Fin m, ((-1 : ℤ) ^ (m + 1 + ((w : ℕ) + 1))) •
        (qminor E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bE e v) u * E (v w) es)) =
      -(∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * Tee * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es)) + Z +
      -(∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0) := by
    rw [Finset.sum_comm (f := fun w w' => ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0), hZ, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [qm_rowW E hFC hFR hLR hSk hE e es v hB, add_mul, add_mul, smul_add, smul_add]
    congr 1
    · congr 1
      · rw [qm_dropS E hFR hSk hE, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Tm_ne E _ (hvs x).symm, mul_smul_comm, smul_mul_assoc, smul_smul, ← pow_add, ← zsmul_eq_mul, ← neg_smul,
          ← mul_assoc, Tm_comm E hE _ hee (hve x)]
        congr 1
        rw [sgn_congr (b := (w : ℕ) + (x : ℕ) + 1) (by omega), pow_succ]
        ring
      · rw [smul_mul_assoc, smul_smul, ← pow_add, sgn_congr (b := (w : ℕ)) (by omega)]
    · rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun W _ => ?_)
      rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun X' _ => ?_)
      split_ifs with h
      · rw [smul_mul_assoc, smul_smul, ← zsmul_eq_mul, ← neg_smul, ← mul_assoc, ← pow_add]
        congr 1
        rw [sgn_congr (b := 1) (by omega)]
        ring
      · simp
  rw [L1, L2, L3, R5]
  abel
end Formalism.FourierDecayAlt.P.Qx6

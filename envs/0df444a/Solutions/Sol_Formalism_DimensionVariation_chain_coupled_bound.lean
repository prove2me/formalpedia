-- Prove2me | solution 1 for Formalism.DimensionVariation.chain_coupled_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:19.053532+00:00
-- url     : https://prove2.me/submissions/f92bf97f-8598-4a8a-a203-7cec94081ff3

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_cbSq_nonneg
import Theorems.Thm_Formalism_DimensionVariation_CB_pos_pair
import Theorems.Thm_Formalism_DimensionVariation_CB_nrm_le_sqrt
import Theorems.Thm_Formalism_DimensionVariation_sharp_norm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mulVecLin_ne_zero
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_mulVecLin
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_nonneg
import Theorems.Thm_Formalism_DivisionValues_composition_norm_at_place
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_opNormAt_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DimensionVariation
theorem _root_.solution : ChainCB := by
  intro K _ _ _ m c Xc Kj AA Cl _ _ W _ _ γ Φ ε T hcl tmax hyp kU hkU
  obtain ⟨hX, hγ, hΦ, hint, hε, hT, ht0, hh⟩ := hyp
  have hnn : ∀ j v, 0 ≤ cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v =>
    cbSq_nonneg (Cl j.castSucc) (Cl j.succ) _ _ _ (ht0 j v) (hh _) (hh _)
  have hop : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v := by
    intro j v
    rw [hkU, opNormAt_mulVecLin]
    refine nrm_le_sqrt _ _ (hX _ v) _ _ (hnn j v) fun y => ?_
    rw [← hΦ, ← hΦ, hint]
    exact (sharp_norm (AA j.castSucc) (AA j.succ) (Cl j.castSucc) (Cl j.succ) (W j.castSucc v)
      (W j.succ v) (γ j.castSucc) (γ j.succ) (ε j v) (T j v) (hcl j.castSucc) (hcl j.succ) (tmax j v)
      (hγ _) (hγ _) (hε j v) (hT j v) (ht0 j v) (hh _) (hh _)).1 _
  have hk2 : ∀ j v, kU j v ^ 2 = cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v => by
    rw [hkU, Real.sq_sqrt (hnn j v)]
  refine ⟨hop, hk2, fun hne => ?_⟩
  have key := (Formalism.DivisionValues.composition_norm_at_place K m c Xc hX Kj).1
  have hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos _ _ _ _ (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hjpos : ∀ j v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    intro j v
    have hprod := (hpos v).trans_le (key v)
    exact lt_of_le_of_ne (opNormAt_nonneg _ _ _ _ _ _)
      (Finset.prod_ne_zero_iff.1 hprod.ne' j (Finset.mem_univ j)).symm
  have hfac : ∀ j v, 0 < (Fintype.card (AA j.castSucc) : ℝ) ∧ 0 < (Fintype.card (AA j.succ) : ℝ) ∧
      0 < hcl j.castSucc ∧ 0 < hcl j.succ ∧ 0 < tmax j v := by
    intro j v
    have h0 : 0 < cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
        (hcl j.castSucc) (hcl j.succ) (tmax j v) := by
      rw [← hk2]; exact pow_pos ((hjpos j v).trans_le (hop j v)) 2
    rw [cbSq] at h0
    obtain ⟨h1, h2⟩ := pos_pair h0 (ht0 j v)
    rw [mul_comm] at h1
    obtain ⟨h3, h4⟩ := pos_pair h1 (by positivity)
    obtain ⟨h5, h6⟩ := pos_pair h4 (Nat.cast_nonneg _)
    obtain ⟨a⟩ := Fintype.card_pos_iff.1 (Nat.cast_pos.1 h6)
    obtain ⟨h7, h8⟩ := pos_pair h3 ((Nat.cast_nonneg _).trans (hh j.succ a))
    exact ⟨h5, h6, h7, h8, h2⟩
  refine ⟨hfac, fun j v => ?_, fun v => ?_, fun v => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hfac j v
    rw [hk2, cbSq, Real.log_mul (by positivity) h5.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
    ring
  · rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
  · exact Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2)
  · rw [Formalism.HN.htMap]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (by positivity)
    refine le_trans ?_ (Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2))
    rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
end Formalism.DimensionVariation

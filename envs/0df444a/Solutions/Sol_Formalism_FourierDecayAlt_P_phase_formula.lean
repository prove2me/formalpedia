-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:53.077658+00:00
-- url     : https://prove2.me/submissions/5b3fc518-07a0-4b54-ae7e-dc01b810e97f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PhaseFormula := by
  intro m t ht p
  obtain ⟨a, v, b⟩ := p
  have h1 : subSum (lowRow a) = a (Fin.last m) := by
    rw [subSum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, Fin.succ_last, lowRow, blk_lc]
    intro i _
    have hne : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
    rw [Fin.succ_castSucc, lowRow, blk_cc, Matrix.one_apply_ne hne]
  have h2 : rhoOf t a v 0 = t * a (Fin.last m) := by
    simp only [rhoOf, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, wMat_mul_apply]
    congr 1
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp [upper, strictUpper]
    · intro i _ hi
      have hne : i.rev ≠ 0 := by
        intro h
        apply hi
        rw [← Fin.rev_rev i, h, Fin.rev_zero]
      have hnl : ¬ i.rev < 0 := by simp
      simp [upper, strictUpper, Matrix.one_apply_ne hne]
    · simp
  have h3 : ∀ k : Fin (m + 1), xOf (Xof t v) (t • b) k = t * blk (upper v) b 0 1 k.castSucc k.succ := by
    intro k
    rw [xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl]; simp
    · rw [Fin.succ_castSucc, blk_cc, blk_cc]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Xof, upper, Matrix.one_apply_ne hne]
  show subSum (lowRow a) + superSum (blk (upper v) b 0 1) =
    (rhoOf t a v 0 + ∑ k, xOf (Xof t v) (t • b) k) / t
  rw [h1, h2, superSum, Finset.sum_congr rfl (fun k _ => h3 k), ← Finset.mul_sum]
  field_simp
end Formalism.FourierDecayAlt.P

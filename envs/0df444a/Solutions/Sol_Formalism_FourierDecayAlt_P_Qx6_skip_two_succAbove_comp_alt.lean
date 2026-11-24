-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.skip_two_succAbove_comp_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:59.651954+00:00
-- url     : https://prove2.me/submissions/e02a84c8-dddf-4c41-ad3a-700f07b5cb68

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution {t : ℕ} (b : Fin (t + 2)) (a : Fin (t + 1)) :
    (skip2 (min (b.succAbove a) b) (max (b.succAbove a) b) : Fin t → Fin (t + 2)) =
      b.succAbove ∘ a.succAbove := by
  funext j
  apply Fin.ext
  by_cases h : a.castSucc < b
  · have h1 : b.succAbove a = a.castSucc := Fin.succAbove_of_castSucc_lt _ _ h
    have h2 : min (b.succAbove a) b = a.castSucc := by rw [h1]; exact min_eq_left h.le
    have h3 : max (b.succAbove a) b = b := by rw [h1]; exact max_eq_right h.le
    rw [h2, h3]
    simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Function.comp] at h ⊢
    split_ifs <;> simp at * <;> omega
  · have h' : b ≤ a.castSucc := not_lt.mp h
    have h1 : b.succAbove a = a.succ := Fin.succAbove_of_le_castSucc _ _ h'
    have h4 : b ≤ a.succ := h'.trans (Fin.castSucc_lt_succ).le
    have h2 : min (b.succAbove a) b = b := by rw [h1]; exact min_eq_right h4
    have h3 : max (b.succAbove a) b = a.succ := by rw [h1]; exact max_eq_left h4
    rw [h2, h3]
    simp only [skip2, Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.val_castSucc, Function.comp, Fin.val_succ] at h' ⊢
    split_ifs <;> simp at * <;> omega
end Formalism.FourierDecayAlt.P.Qx6

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:40.805336+00:00
-- url     : https://prove2.me/submissions/f59ed139-0e9d-40d7-baef-1028c37db27c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_e_ne_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_o
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_dd_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_dd_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_dd_o
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_tri
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_mul_weyl_cell_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_weyl_cell_conjTranspose_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_col_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_col_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_row_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpk_row_es

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (l : Fin r) {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  have hne := e_ne_es (k := k) l
  have hcs : (starRingEnd ℂ) c ≠ 0 := star_ne_zero.2 hc
  show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r
  ext p q
  rw [mul_weyl_cell_apply, weyl_cell_conjTranspose_mul_apply]
  rcases tri l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_e, hpk_row_es, hpk_row_e]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hne, hne.symm]
    · subst h'
      simp [sw_es, dd_es, hcs]
    · simp [sw_o l h1' h2', h1', h2']
  · subst h
    rw [sw_es, dd_es, hpk_row_es, hpk_row_e]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, dd_e, hc]
    · subst h'
      simp [sw_es, hne, hne.symm]
    · simp [sw_o l h1' h2', h1', h2']
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hpk_col_e, hpk_col_es, h1, h2]
    · subst h'
      simp [sw_es, hpk_col_e, hpk_col_es, h1, h2]
    · simp [sw_o l h1' h2', dd_o l c h1' h2']
end Formalism.FourierDecayAlt.P.Qx3

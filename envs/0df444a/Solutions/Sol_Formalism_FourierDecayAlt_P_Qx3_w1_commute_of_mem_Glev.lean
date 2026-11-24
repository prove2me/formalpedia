-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.w1_commute_of_mem_Glev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:07:54.123034+00:00
-- url     : https://prove2.me/submissions/7bfee4df-e7cb-413b-8755-8491c7ed8626

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_weyl_cell_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_tau_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_tau_es
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_of_fix
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_row_of_fixed_col


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
theorem _root_.solution (l : Fin r) (c : ℂ) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g = g * w1 k r l c := by
  have hne := e_ne_es (k := k) l
  have hl : l.val < (l.succ : Fin (r + 1)).val := by simp
  have ce : ∀ p, g p (eI k r l) = if p = eI k r l then 1 else 0 := WeylGroupFacts.col_of_fix (hg.2 l hl).1
  have ces : ∀ p, g p (esI k r l) = if p = esI k r l then 1 else 0 := WeylGroupFacts.col_of_fix (hg.2 l hl).2
  have res : ∀ j, g (esI k r l) j = if esI k r l = j then 1 else 0 := by
    have := WeylGroupFacts.row_of_fixed_col hg.1 (eI k r l) ce
    rwa [tau_e] at this
  have re : ∀ j, g (eI k r l) j = if eI k r l = j then 1 else 0 := by
    have := WeylGroupFacts.row_of_fixed_col hg.1 (esI k r l) ces
    rwa [tau_es] at this
  ext p q
  rw [mul_weyl_cell_apply, weyl_cell_mul_apply]
  rcases tri l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_es, res, re]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hne, hne.symm]
    · subst h'
      simp [sw_es, dd_es]
    · simp [sw_o l h1' h2', Ne.symm h1', Ne.symm h2']
  · subst h
    rw [sw_es, dd_e, res, re]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, dd_e]
    · subst h'
      simp [sw_es, hne, hne.symm]
    · simp [sw_o l h1' h2', Ne.symm h1', Ne.symm h2']
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, ce, ces, h1, h2]
    · subst h'
      simp [sw_es, ce, ces, h1, h2]
    · simp [sw_o l h1' h2', dd_o l c h1' h2']
end Formalism.FourierDecayAlt.P.Qx3

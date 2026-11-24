-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.w1_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:00:00.46917+00:00
-- url     : https://prove2.me/submissions/c95a2e55-dfb4-4300-9e7f-2639b2e7974b

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
theorem _root_.solution (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) :
    w1 k r l c p q = if p = sw k l q then dd k l c q else 0 := by
  have hne := e_ne_es (k := k) l
  rcases tri l q with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_e]
    unfold w1
    by_cases hp : p = esI k r l
    · simp [hp]
    · simp [hp, hne]
  · subst h
    rw [sw_es, dd_es]
    unfold w1
    by_cases hp : p = eI k r l
    · simp [hp, hne, hne.symm]
    · simp [hp, hne.symm]
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    unfold w1
    by_cases hp : p = q
    · subst hp
      simp [h1, h2]
    · simp [hp, h1, h2]
end Formalism.FourierDecayAlt.P.Qx3

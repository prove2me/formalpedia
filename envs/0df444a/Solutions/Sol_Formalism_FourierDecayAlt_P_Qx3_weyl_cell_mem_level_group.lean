-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_level_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:07:54.885807+00:00
-- url     : https://prove2.me/submissions/9cd1fbc8-aa35-4f87-a734-5c429fb4bf74

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_weyl_cell_mem_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_reflection_fixes_basis_vector

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
theorem _root_.solution (l : Fin r) {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  refine ⟨weyl_cell_mem_unitary l hc, fun a ha => ?_⟩
  have ha' : a.val < l.val := ha
  have hl := l.isLt
  constructor
  · apply reflection_fixes_basis_vector <;> simp only [eI, esI, ne_eq, Fin.ext_iff] <;> omega
  · apply reflection_fixes_basis_vector <;> simp only [eI, esI, ne_eq, Fin.ext_iff] <;> omega
end Formalism.FourierDecayAlt.P.Qx3

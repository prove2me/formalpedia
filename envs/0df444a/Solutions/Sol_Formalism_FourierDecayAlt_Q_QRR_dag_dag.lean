-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.dag_dag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:43:32.624611+00:00
-- url     : https://prove2.me/submissions/28e98a7d-2a37-4527-98c4-3c89d53e424a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hpk_inv
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (A : Mx k r) : dag k r (dag k r A) = A := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have h2' : ∀ M : Mx k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  unfold dag
  rw [hpk_inv]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc, h2', h2,
    Matrix.mul_one]
end Formalism.FourierDecayAlt.Q.QRR

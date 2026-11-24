-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_bE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:17.992482+00:00
-- url     : https://prove2.me/submissions/f4de053e-297c-480d-acad-d6498811f8cd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_bS_eq

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
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hSk : QSkewRow) {t : ℕ} (f : Fin t → Fin n) (e : Fin n) (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = ((-1 : ℤ) ^ t) • qminor E (bS f e) b u := by
  rw [qm_bS_eq E hSk f e b u, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
end Formalism.FourierDecayAlt.P.Qx6

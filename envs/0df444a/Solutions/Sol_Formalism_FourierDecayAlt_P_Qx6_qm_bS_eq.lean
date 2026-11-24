-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_bS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:57.982488+00:00
-- url     : https://prove2.me/submissions/9aa22344-592e-413c-abeb-c2e8cd52819f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_cyc

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
    qminor E (bS f e) b u = ((-1 : ℤ) ^ t) • qminor E (bE e f) b u := by
  have hs : Equiv.Perm.sign (cycleToLast t 0) = (-1) ^ t := by
    simp only [cycleToLast, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Fin.rev_zero, Fin.sign_cycleRange, Fin.val_last]
    rw [mul_left_comm, Int.units_mul_self, mul_one]
  rw [← bE_cyc, hSk A n (t + 1) E (bE e f) b (cycleToLast t 0) u, hs, zsmul_eq_mul]
  push_cast
  rfl
end Formalism.FourierDecayAlt.P.Qx6

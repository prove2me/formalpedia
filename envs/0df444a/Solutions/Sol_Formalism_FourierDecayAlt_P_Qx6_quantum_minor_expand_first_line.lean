-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.quantum_minor_expand_first_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:19.0069+00:00
-- url     : https://prove2.me/submissions/8d21822b-0335-43ad-9314-2c6fa9e4f9f0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_comp_succ
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
theorem _root_.solution (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (f : Fin t → Fin n) (e : Fin n)
    (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), ((-1 : ℤ) ^ (t + (x : ℕ))) •
      (Tm E (u - (t : ℂ)) e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  rw [qm_bS_eq E hSk f e b u, hFR A n t E hE (bE e f) b u, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [bE_zero, bE_comp_succ, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← pow_add]
end Formalism.FourierDecayAlt.P.Qx6

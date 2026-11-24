-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.quantum_minor_expand_last_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:37.420693+00:00
-- url     : https://prove2.me/submissions/d8d974a2-9447-45c1-a37c-12f576ebe258

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_comp_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_bE_eq

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
theorem _root_.solution (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (f : Fin t → Fin n) (e : Fin n)
    (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bE e f) b u = ∑ x : Fin (t + 1), ((-1 : ℤ) ^ (x : ℕ)) •
      (qminor E f (b ∘ x.succAbove) (u - 1) * Tm E u e (b x)) := by
  rw [qm_bE_eq E hSk f e b u, hLR A n t E hE (bS f e) b u, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hz : ((-1 : ℤ) ^ t) * (-1) ^ (t + (x : ℕ)) = (-1) ^ (x : ℕ) := by
    rw [← pow_add, show t + (t + (x : ℕ)) = (x : ℕ) + 2 * t by ring, pow_add, pow_mul]
    simp
  rw [bS_comp_castSucc, bS_last, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, hz]
end Formalism.FourierDecayAlt.P.Qx6

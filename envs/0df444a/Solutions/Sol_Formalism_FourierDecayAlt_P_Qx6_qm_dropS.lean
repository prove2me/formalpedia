-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_dropS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:49.742111+00:00
-- url     : https://prove2.me/submissions/2c22683c-ffd3-485e-8c5a-d42ccde0db27

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sgn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_quantum_minor_expand_first_line

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
theorem _root_.solution (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) : ∀ {m : ℕ} (v b : Fin m → Fin n) (s : Fin n)
    (w : Fin m) (u : ℂ),
    qminor E (bS v s ∘ w.castSucc.succAbove) b u = ∑ x : Fin m, ((-1 : ℤ) ^ (m + 1 + (x : ℕ))) •
      (Tm E (u - (m : ℂ) + 1) s (b x) * qminor E (v ∘ skip1 w) (b ∘ skip1 x) u)
  | 0, _, _, _, w, _ => w.elim0
  | m + 1, v, b, s, w, u => by
    rw [bS_succAbove_castSucc, quantum_minor_expand_first_line E hFR hSk hE]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [sgn_congr (b := m + 1 + 1 + (x : ℕ)) (by omega)]
    have e1 : u - ((m + 1 : ℕ) : ℂ) + 1 = u - (m : ℂ) := by push_cast; ring
    rw [e1]
    rfl
end Formalism.FourierDecayAlt.P.Qx6

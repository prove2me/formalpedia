-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_drop2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:57.586196+00:00
-- url     : https://prove2.me/submissions/b2f7bda8-0cc0-49ce-b856-729127dd5f3a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_succAbove_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_quantum_minor_expand_last_line
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_dropS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (g : Fin t → Fin n)
    (b : Fin (t + 1) → Fin n) (e s : Fin n) (w : Fin t) (u : ℂ) :
    qminor E (bE e (bS g s) ∘ w.castSucc.succ.succAbove) b u =
      ∑ x' : Fin (t + 1), ∑ x : Fin t, ((-1 : ℤ) ^ ((x' : ℕ) + (t + 1 + (x : ℕ)))) •
        (Tm E (u - 1 - (t : ℂ) + 1) s (b (x'.succAbove x)) *
          qminor E (g ∘ skip1 w) ((b ∘ x'.succAbove) ∘ skip1 x) (u - 1) * Tm E u e (b x')) := by
  rw [bE_succAbove_succ, quantum_minor_expand_last_line E hLR hSk hE]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [qm_dropS E hFR hSk hE, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, smul_smul, ← pow_add]
  rfl
end Formalism.FourierDecayAlt.P.Qx6

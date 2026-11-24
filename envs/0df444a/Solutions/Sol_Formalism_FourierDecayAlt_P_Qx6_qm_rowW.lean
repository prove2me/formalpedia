-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.qm_rowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:19.488842+00:00
-- url     : https://prove2.me/submissions/b973ce62-c3ae-44ad-ad09-dd86412ff26b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_two_succAbove_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bE_succAbove_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_bS_succAbove_castSucc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sgn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Tm_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expFCE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sum3conv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_two_comp_skip_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_drop2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
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
theorem _root_.solution (hFC : ExpFirstCol) (hFR : ExpFirstRow) (hLR : ExpLastRow) (hSk : QSkewRow) (hE : GlRel E)
    (e es : Fin n) : ∀ {m : ℕ} (v : Fin m → Fin n), IsBorder e es v → ∀ (w : Fin m) (u : ℂ),
    qminor E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bE e v) u =
      Tm E u e e * qminor E (bS v es ∘ w.castSucc.succAbove) v (u - 1) +
      ((-1 : ℤ) ^ m) • (E es e * qminor E (bE e v ∘ w.succ.succAbove) v (u - 1)) +
      ∑ W : Fin m, ∑ X : Fin m, ∑ X' : Fin m, if W ≠ w ∧ X ≠ X' then
        ((-1 : ℤ) ^ (m + 1 + (w : ℕ)) * (sg2 W w * sg2 X X')) •
          (E (v W) e * E es (v X) *
            qminor E (v ∘ skip2 (min W w) (max W w)) (v ∘ skip2 (min X X') (max X X')) (u - 2) * E e (v X'))
        else 0
  | 0, _, _, w, _ => w.elim0
  | m + 1, v, hB, w, u => by
    obtain ⟨_, hee, hve, hvs⟩ := hB
    rw [sum3conv, bE_succAbove_succ, bS_succAbove_castSucc, expFCE E hFC, Fin.sum_univ_castSucc,
      add_assoc (Tm E u e e * _)]
    congr 1
    rw [add_comm (Finset.sum _ _)]
    congr 1
    · rw [bS_last, Tm_ne E _ hee.symm, bE_succAbove_succ, bS_succAbove_last, bE_succAbove_succ, Fin.val_last]
    · refine Finset.sum_congr rfl (fun w' _ => ?_)
      rw [qm_drop2 E hFR hLR hSk hE, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x' _ => ?_)
      rw [Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [bS_castSucc, Function.comp, Tm_ne E _ (hve _), Tm_ne E _ (hvs _).symm, Tm_ne E _ (hve _).symm,
        mul_smul_comm, smul_smul, sign_two_succAbove_left, sign_two_succAbove_left, skip_two_comp_skip_one, skip_two_comp_skip_one, show u - 1 - 1 = u - 2 by ring,
        Fin.val_castSucc, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      · exact sgn_congr (by omega)
      · simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Qx6

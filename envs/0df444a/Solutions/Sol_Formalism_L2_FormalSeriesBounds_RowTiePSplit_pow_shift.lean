-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.pow_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:49.942384+00:00
-- url     : https://prove2.me/submissions/d284f2a6-3e2d-40ad-a1f5-1ca58c6c03ae

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (k : ℕ) :
    (N + B) ^ k *ᵥ w = (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k *ᵥ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.add_mulVec, Matrix.add_mulVec]
    congr 1
    have hc : Commute N ((algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k) :=
      ((show Commute (algebraMap K (Matrix (Fin n) (Fin n) K) lam) N from Algebra.commutes lam N).symm.add_right
        hNB).pow_right k
    rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, alg_mulVec1]
end Formalism.L2.FormalSeriesBounds.RowTiePSplit

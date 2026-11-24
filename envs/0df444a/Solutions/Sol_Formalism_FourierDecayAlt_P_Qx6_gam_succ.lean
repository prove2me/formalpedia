-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.gam_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:49.75453+00:00
-- url     : https://prove2.me/submissions/a4c26cb8-1187-4598-b15d-7e0f44e09707

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (l : Fin r) (c : Fin r → ℂ) :
    gam k r l.succ c = gam k r l.castSucc c * ‖c l‖ ^ (Mdim k r l - 1) := by
  have key : ∀ a : Fin r, (if a.val < l.succ.val then ‖c a‖ ^ (Mdim k r a - 1) else (1 : ℝ)) =
      (if a.val < l.castSucc.val then ‖c a‖ ^ (Mdim k r a - 1) else 1) *
        (if a = l then ‖c a‖ ^ (Mdim k r a - 1) else 1) := by
    intro a
    rw [Fin.val_succ, Fin.coe_castSucc]
    by_cases h1 : a = l
    · subst h1
      simp
    · have h3 : a.val ≠ l.val := fun h => h1 (Fin.ext h)
      by_cases h2 : a.val < l.val
      · rw [if_pos (show a.val < l.val + 1 by omega), if_pos h2, if_neg h1, mul_one]
      · rw [if_neg (show ¬ a.val < l.val + 1 by omega), if_neg h2, if_neg h1, mul_one]
  unfold gam
  rw [Finset.prod_congr rfl (fun a _ => key a), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp
end Formalism.FourierDecayAlt.P.Qx6

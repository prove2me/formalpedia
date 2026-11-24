-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_brk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:19.197291+00:00
-- url     : https://prove2.me/submissions/3b7ded57-9e5d-4f20-90ac-b8083caa34c9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_prod_minor
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brk mu I = ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      algebraMap (MvPolynomial (Fin n × Fin n) ℤ) (GLCoord ℤ n) (rename Prod.swap (qa_P ℤ I)) := by
  unfold brk TMat minorC
  rw [← qa_prod_minor, map_prod]
end Formalism.InvariantFactorPaths.ColumnFamilies

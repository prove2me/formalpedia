-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_SMu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:46.3968+00:00
-- url     : https://prove2.me/submissions/43142c3f-c741-46eb-b8f0-ad02e6d3d848

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brk_Phi
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_eq_span_tableauBideterminant


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
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    SMu mu = (dualWeyl ℤ n n (qa_nu mu)).map
      (qa_PhiZ n ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) := by
  rw [dualWeyl_eq_span_tableauBideterminant ℤ hmu, Submodule.map_span, ← Set.range_comp]
  unfold SMu
  congr 2
  funext I
  exact qa_brk_Phi mu I
end Formalism.InvariantFactorPaths.ColumnFamilies

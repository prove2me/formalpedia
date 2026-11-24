-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:37.067789+00:00
-- url     : https://prove2.me/submissions/f2300efc-ba46-4e23-bdff-b2849171ff34

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge

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
theorem _root_.solution (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R
end Formalism.InvariantFactorPaths.ColumnFamilies

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_theorem_of_clauses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.807447+00:00
-- url     : https://prove2.me/submissions/edf784e8-93b4-41da-a0c0-3f4f78939eb1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (h1 : FiltrationStandardSpan) (h2 : FiltrationTypeIntersection) (h3 : FiltrationCoactionStable) (h4 : FiltrationDirectSummand) (h5 : FiltrationMaximalQuotient) (h6 : HighestVectorsEqLattice) : ColumnFamilyFiltrationProperties :=
  fun n _ M CF pi hpi => ⟨h1 n M CF pi hpi, h2 n M CF pi hpi, h3 n M CF pi hpi, h4 n M CF pi hpi,
    fun mu hmu hmax => ⟨h5 n M CF pi hpi mu hmu hmax, h6 n M CF mu (hpi.1 mu hmu)⟩⟩
end Formalism.InvariantFactorPaths.ColumnFamilies

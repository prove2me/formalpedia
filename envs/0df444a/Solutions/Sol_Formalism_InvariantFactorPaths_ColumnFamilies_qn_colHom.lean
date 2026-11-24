-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_colHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:04.281026+00:00
-- url     : https://prove2.me/submissions/fe789601-6b4f-462d-93bb-b87fcb9dcfef

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) R)
    (hF : F ∈ dualWeyl R n n ν) : IsWeightedHomogeneous (colW n n) F ν :=
  (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
end Formalism.InvariantFactorPaths.ColumnFamilies

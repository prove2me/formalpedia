-- Prove2me | solution 1 for DeletionCode.FiniteConflictGraph.vertex_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:35:04.588543+00:00
-- url     : https://prove2.me/submissions/cfd8a262-3365-408e-9636-df242a726274

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}
namespace DeletionCode.FiniteConflictGraph
theorem _root_.solution {t k : ℕ} {label : Bits n → H} (x : Vertex t k label) :
    Windows.KUnique (padBits x.val) n k := x.property.1
end DeletionCode.FiniteConflictGraph

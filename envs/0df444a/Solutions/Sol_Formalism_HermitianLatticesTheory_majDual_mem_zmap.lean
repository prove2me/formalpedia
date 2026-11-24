-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_mem_zmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:55.405884+00:00
-- url     : https://prove2.me/submissions/07c4baec-db0c-4daa-820e-56e8b72bb332

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {R W : Type*} [Ring R] [Module R V] [AddCommGroup W] (f : V →+ W)
    (M : Submodule R V) (w : W) : w ∈ zmap f M ↔ ∃ y ∈ M, f y = w := by
  exact Iff.rfl
end Formalism.HermitianLatticesTheory

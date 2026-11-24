-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_invDiffSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:53.759669+00:00
-- url     : https://prove2.me/submissions/70bccc48-cce3-45e1-9ab8-ae3af7c7e8cf

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_memI

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : invDiffSub K = (majDualI K : Submodule (RingOfIntegers K) K) := by
  have e : invDiff K = ((majDualI K : Submodule (RingOfIntegers K) K) : Set K) := by
    ext a
    exact (majDual_memI a).symm
  rw [invDiffSub, e, Submodule.span_eq]
end Formalism.HermitianLatticesTheory

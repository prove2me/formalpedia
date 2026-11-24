-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.6198+00:00
-- url     : https://prove2.me/submissions/d47f0d20-5371-4eb8-9cff-e22673291e40

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h y (∑ i ∈ s, f i)) = ∑ i ∈ s, Algebra.trace ℚ K (h y (f i)) := by
  rw [map_sum, map_sum]
end Formalism.HermitianLatticesTheory

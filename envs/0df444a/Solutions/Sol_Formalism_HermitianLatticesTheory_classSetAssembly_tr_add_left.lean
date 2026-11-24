-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:57.361374+00:00
-- url     : https://prove2.me/submissions/7a1f4d8c-d513-4a8f-923d-76b4c07e6479

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x + y) z) = Algebra.trace ℚ K (h x z) + Algebra.trace ℚ K (h y z) := by
  simp only [map_add, LinearMap.add_apply]
end Formalism.HermitianLatticesTheory

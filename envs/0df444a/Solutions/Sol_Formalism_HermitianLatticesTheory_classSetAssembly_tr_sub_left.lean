-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.462672+00:00
-- url     : https://prove2.me/submissions/e99052ab-49f9-43ab-809d-c14b9ef6c58f

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
    Algebra.trace ℚ K (h (x - y) z) = Algebra.trace ℚ K (h x z) - Algebra.trace ℚ K (h y z) := by
  simp only [map_sub, LinearMap.sub_apply]
end Formalism.HermitianLatticesTheory

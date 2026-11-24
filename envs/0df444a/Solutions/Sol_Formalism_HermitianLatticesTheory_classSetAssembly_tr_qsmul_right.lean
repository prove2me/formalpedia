-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.79362+00:00
-- url     : https://prove2.me/submissions/3cb34380-4354-4b6d-900d-07cf4c58e1a4

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_ratCast_mul

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h x ((q : K) • y)) = q * Algebra.trace ℚ K (h x y) := by
  rw [map_smul, smul_eq_mul, classSetAssembly_ratCast_mul]
end Formalism.HermitianLatticesTheory

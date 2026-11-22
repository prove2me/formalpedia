-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:45.687806+00:00
-- url     : https://prove2.me/submissions/1a7caa7b-8bad-48a4-97fc-88f5e55bafd6

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
    Algebra.trace ℚ K (h ((q : K) • x) y) = q * Algebra.trace ℚ K (h x y) := by
  have e : h ((q : K) • x) y = (q : K) * h x y := by
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_ratCast]
  rw [e, classSetAssembly_ratCast_mul]
end Formalism.HermitianLatticesTheory

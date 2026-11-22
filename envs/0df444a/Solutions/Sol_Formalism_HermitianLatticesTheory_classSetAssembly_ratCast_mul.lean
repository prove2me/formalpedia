-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_ratCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:14.464957+00:00
-- url     : https://prove2.me/submissions/51decb74-5107-4780-bd5d-2f3abb8c3321

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
theorem _root_.solution (q : ℚ) (a : K) :
    Algebra.trace ℚ K ((q : K) * a) = q * Algebra.trace ℚ K a := by
  have e : (q : K) * a = q • a := by
    rw [Algebra.smul_def, eq_ratCast]
  rw [e, map_smul, smul_eq_mul]
end Formalism.HermitianLatticesTheory

-- Prove2me | solution 1 for Formalism.MainNotions.J.sum_ef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:58.843056+00:00
-- url     : https://prove2.me/submissions/0e9cbd28-6a33-451d-a865-c20c4548b0be

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_pI_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K),
      (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P = Module.finrank ℚ K := by
  haveI := pI_max p hp
  exact Ideal.sum_ramification_inertia (𝓞 K) ℚ K (pI_ne_bot p hp)
end Formalism.MainNotions.J

-- Prove2me | solution 1 for Formalism.L2.Pj.nval_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:52.04266+00:00
-- url     : https://prove2.me/submissions/70e00921-8a15-46b0-8167-8776607939df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable {V}
variable (V)
variable {V}
namespace Formalism.L2.Pj
theorem _root_.solution (e : ℕ) (x : K') : nval V e x ≠ ⊥ := by
  unfold nval; split_ifs <;> simp
end Formalism.L2.Pj

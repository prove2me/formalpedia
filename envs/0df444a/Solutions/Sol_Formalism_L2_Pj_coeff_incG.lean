-- Prove2me | solution 1 for Formalism.L2.Pj.coeff_incG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:37.536593+00:00
-- url     : https://prove2.me/submissions/6e331ea3-d496-4fe5-899f-0859380369fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_incG_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
open Classical
namespace Formalism.L2.Pj
theorem _root_.solution (m : M) (w : W) (F : C w) :
    (incG key C w F).coeff m = if key w = m then (F : R) else 0 := by
  rw [incG_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
end Formalism.L2.Pj

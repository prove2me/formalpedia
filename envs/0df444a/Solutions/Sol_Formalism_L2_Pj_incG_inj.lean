-- Prove2me | solution 1 for Formalism.L2.Pj.incG_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:36.298724+00:00
-- url     : https://prove2.me/submissions/445d2657-553d-4067-b7ea-984fb35acfd9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_coeff_incG

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
namespace Formalism.L2.Pj
theorem _root_.solution (w : W) : Function.Injective (incG key C w) := fun F F' h => by
  have h1 := congrArg (fun x : AddMonoidAlgebra R M => x.coeff (key w)) h
  simp only [coeff_incG, if_true] at h1
  exact Subtype.ext h1
end Formalism.L2.Pj

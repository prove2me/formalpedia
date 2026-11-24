-- Prove2me | solution 1 for Formalism.L2.Pj.incG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:37.382033+00:00
-- url     : https://prove2.me/submissions/77127006-9109-4eb0-b528-16a07199f7ce

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
namespace Formalism.L2.Pj
theorem _root_.solution {w w' u : W} (hu : key u = key w + key w') (F : C w) (F' : C w')
    (h : (F : R) * (F' : R) ∈ C u) : incG key C w F * incG key C w' F' = incG key C u ⟨_, h⟩ := by
  rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, hu]
end Formalism.L2.Pj

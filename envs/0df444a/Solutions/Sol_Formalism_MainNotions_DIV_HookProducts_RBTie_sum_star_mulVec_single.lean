-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.sum_star_mulVec_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:39:03.249626+00:00
-- url     : https://prove2.me/submissions/d9a05847-5983-44c3-96c3-f64cd456e7e7

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (i j : n) :
    ∑ k, star ((C *ᵥ Pi.single i 1) k) * (C *ᵥ Pi.single j 1) k = (Cᴴ * C) i j := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.MainNotions.DIV.HookProducts.RBTie

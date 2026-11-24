-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.star_mulVec_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:52.001972+00:00
-- url     : https://prove2.me/submissions/af891f0e-b574-4eb6-907c-8be1ed4f33de

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (A B : Matrix m m ℂ) (u w : m → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
end Formalism.L2.Pj.DatLin

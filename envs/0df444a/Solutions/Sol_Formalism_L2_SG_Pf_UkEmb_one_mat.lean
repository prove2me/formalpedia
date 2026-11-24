-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.one_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:36.983117+00:00
-- url     : https://prove2.me/submissions/b366a99d-ccd5-4cfa-bb60-f2ce6ac573a1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
include hon
namespace Formalism.L2.SG.Pf.UkEmb
theorem _root_.solution (a b : Fin k) : star (wf a) ⬝ᵥ (J *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ wf b)) =
    (1 : Matrix (Fin k) (Fin k) ℂ) a b := by
  rw [Matrix.one_mulVec, hon, Matrix.one_apply]
end Formalism.L2.SG.Pf.UkEmb

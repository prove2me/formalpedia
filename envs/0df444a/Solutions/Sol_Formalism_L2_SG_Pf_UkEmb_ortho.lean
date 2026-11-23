-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:52.337042+00:00
-- url     : https://prove2.me/submissions/b09f0dd3-795e-4e14-9115-dfc8ef8899a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_entry

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
theorem _root_.solution : (Wm wf)ᴴ * J * Wm wf = 1 := by
  ext a b
  rw [entry, hon, Matrix.one_apply]
end Formalism.L2.SG.Pf.UkEmb

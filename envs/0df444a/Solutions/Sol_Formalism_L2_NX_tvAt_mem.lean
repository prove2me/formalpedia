-- Prove2me | solution 1 for Formalism.L2.NX.tvAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:16.041458+00:00
-- url     : https://prove2.me/submissions/17e6172a-5ef6-4482-85df-0f00bb63caf9

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
import Theorems.Thm_Formalism_L2_NX_mem_Uup
import Theorems.Thm_Formalism_L2_NX_tv_uniTri
import Theorems.Thm_Formalism_L2_NX_tvAt_apply

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
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution [DecidableEq ι] (hr : 2 ≤ r) (x : ι) : tvAt (p := p) hr x ∈ Uup p r := by
  rw [mem_Uup]
  intro y
  rw [tvAt_apply]
  split_ifs
  · exact tv_uniTri hr 1
  · exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩
end Formalism.L2.NX

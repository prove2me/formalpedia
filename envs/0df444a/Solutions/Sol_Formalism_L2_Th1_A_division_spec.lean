-- Prove2me | solution 1 for Formalism.L2.Th1.A.division_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:23:33.295593+00:00
-- url     : https://prove2.me/submissions/bf3b12cb-bf03-411d-bdc0-bec2acd26157

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementO
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DivisionLogarithm
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_L2_Th1_A_compInvMap
import Theorems.Thm_Formalism_L2_Th1_A_compInvSpec
import Theorems.Thm_Formalism_L2_Th1_A_zSerMap
import Theorems.Thm_Formalism_L2_Th1_A_zSerSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : DivSpec.{u, v} := by
  intro R _ W n hn
  obtain ⟨hcc, hc1⟩ := (zSerSpec R W).1 n
  have hu : IsUnit (coeff 1 (zSer W n)) := by rw [hc1]; exact hn
  obtain ⟨h0, hr, hl, h1, -, -⟩ := compInvSpec R (zSer W n) hcc hu
  refine ⟨h0, ?_, hr, hl, ?_, ?_⟩
  · rw [hc1] at h1
    rw [mul_comm]; exact h1
  · intro S _ φ
    have key := compInvMap R S φ (zSer W n) hcc hu
    rw [zSerMap R S φ W n] at key
    exact key
  · intro h2
    subst h2
    rfl
end Formalism.L2.Th1.A

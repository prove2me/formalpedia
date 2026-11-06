-- Prove2me | solution 1 for Eight.ViaGrouping.algPseudocode_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:58:13.595942+00:00
-- url     : https://prove2.me/submissions/80296b54-ef46-4bf7-bd30-f36c0a83cd74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_COUNTp_cost
import Theorems.Thm_Eight_numSat_pos_iff
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {δ M : ℝ} (hδ : 0 < δ) (hM : 1 ≤ M) {S : StepMachine Formula ℤ → StepMachine (List Bool) Bool} (hS : SufficesSparse δ M S) {ℓ : ℕ}
    (hK : 72 / min (δ / (3 * M)) 1 ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ min (δ / (3 * M)) 1 / 12) : Paper.DecidesInSteps (S (COUNTp ℓ)) δ := by
  have hδ' : 0 < min (δ / (3 * M)) 1 := lt_min (by positivity) one_pos
  obtain ⟨A, hA⟩ := COUNTp_cost hδ' (min_le_right _ _) hK hE
  refine hS.2 _ A fun Φ hΦ => ?_
  obtain ⟨T, hrun, hT⟩ := hA Φ hΦ
  -- «Φ is satisfiable if and only if Z > 0»
  refine ⟨T, _, hrun, by rw [Nat.cast_pos]; exact numSat_pos_iff Φ, hT.trans ?_⟩
  gcongr
  · norm_num
  · exact min_le_left _ _
end Eight.ViaGrouping

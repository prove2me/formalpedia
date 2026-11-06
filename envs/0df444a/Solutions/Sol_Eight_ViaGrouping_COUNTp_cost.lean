-- Prove2me | solution 1 for Eight.ViaGrouping.COUNTp_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:47.071203+00:00
-- url     : https://prove2.me/submissions/e697e39f-38d8-4b3a-bc4c-22066f2a26a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_two_le_levelK
import Theorems.Thm_Eight_ViaGrouping_zero_lt_levelG
import Theorems.Thm_Eight_ViaGrouping_CLIQUEp_within
import Theorems.Thm_Eight_ViaGrouping_count_cost_of
import Theorems.Thm_Eight_ViaGrouping_stLemGrouping
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution {δ' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) {ℓ : ℕ} (hK : 72 / δ' ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ δ' / 12) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNTp ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) :=
  ViaGrouping.count_cost_of hδ' hδ'1 (zero_lt_levelG ℓ) hK
    (stLemGrouping (levelK ℓ) (δ' / 12) (CLIQUEp ℓ) (two_le_levelK ℓ) (by positivity) ((CLIQUEp_within ℓ).mono hE))
end Eight.ViaGrouping

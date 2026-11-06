-- Prove2me | solution 1 for Eight.ViaGrouping.COLOR_counts_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:21.024867+00:00
-- url     : https://prove2.me/submissions/b67aaaca-6817-4bb3-a7b5-9dc116dfdf7d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Graph
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Theorems.Thm_Eight_color_counts
import Theorems.Thm_GraphProblems_readC_polyT
import Theorems.Thm_GraphProblems_stAdj
import Theorems.Thm_GraphProblems_stCertForm
import Theorems.Thm_GraphProblems_stCertRead
import Theorems.Thm_GraphProblems_stColor
import Theorems.Thm_GraphProblems_stRead1
import Theorems.Thm_GraphProblems_stShapeColor


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
variable {En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)}
namespace Eight.ViaGrouping
theorem _root_.solution (h : EngineCounts En) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)) ∧
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ T : ℕ, (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) (SatK.binary (n * k) (numColorings G k)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨ℓ, τ, ⟨hE⟩, c, hc⟩ := h (max k 2) (le_max_of_le_right (by norm_num)) (δ / k) (by positivity)
  refine ⟨ℓ, τ, ⟨IsPolyT.mapIn (M := En (max k 2) ℓ τ) (readC_polyT stCertRead stCertForm k)⟩, c * k ^ c + c, fun n G => ?_⟩
  have h := color_counts stRead1 stShapeColor k hk hc n G
  rwa [stColor stAdj k n G] at h
end Eight.ViaGrouping

-- Prove2me | solution 1 for Eight.Width.stWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:12:28.175254+00:00
-- url     : https://prove2.me/submissions/f1cd7fe5-7d24-4e24-89ed-6ce2447b6efd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_splitAll_width
import Theorems.Thm_Eight_Width_length_splitAll
import Theorems.Thm_Eight_Width_numFresh_le
import Theorems.Thm_Eight_Width_numFresh_lift
import Theorems.Thm_Eight_Width_length_freshFin
import Theorems.Thm_Eight_Width_numSat_widthReduce

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution : StWidth := by
  intro n φ
  refine ⟨⟨fun C hC => ?_, List.nodup_dedup _⟩, numSat_widthReduce φ, fun k hk => ?_⟩
  · exact splitAll_width (lift _ φ) (freshFin n _) (by rw [length_freshFin, numFresh_lift]) C (List.mem_dedup.1 hC)
  · have h1 := numFresh_le k φ hk
    refine ⟨h1, ?_⟩
    calc (widthReduce φ).length ≤ (splitAll (freshFin n (numFresh φ)) (lift (numFresh φ) φ)).length :=
          (List.dedup_sublist _).length_le
      _ = φ.length + 3 * numFresh φ := by
          rw [length_splitAll _ _ (by rw [length_freshFin, numFresh_lift]), numFresh_lift]
          simp [lift]
      _ ≤ φ.length + 3 * ((k - 3) * φ.length) := by omega
end Eight.Width

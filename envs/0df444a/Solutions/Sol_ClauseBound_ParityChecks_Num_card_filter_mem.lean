-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.card_filter_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:15.541104+00:00
-- url     : https://prove2.me/submissions/ccdbe3da-cebb-43d4-acfe-ababfcf57887

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {m : ℕ} {L : Chk} (hn : L.Nodup) (hl : ∀ x ∈ L, x < m) : #(univ.filter fun x : Fin m => x.val ∈ L) = L.length := by
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, List.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro ha; exact ⟨⟨a, hl a ha⟩, ha, rfl⟩
end ClauseBound.ParityChecks.Num

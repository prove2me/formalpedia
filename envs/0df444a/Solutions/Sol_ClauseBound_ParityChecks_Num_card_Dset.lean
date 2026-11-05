-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.card_Dset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:25.343929+00:00
-- url     : https://prove2.me/submissions/8f84212d-73ef-4bdc-bfc8-a5f5b3fbafec

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
theorem _root_.solution (m e : ℕ) : #(Dset m e) = m - e := by
  unfold Dset
  rw [← Nat.card_Ico, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.isLt⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨a, h2⟩, h1, rfl⟩
end ClauseBound.ParityChecks.Num

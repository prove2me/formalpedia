-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.needCut_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:33.034118+00:00
-- url     : https://prove2.me/submissions/759e06a5-dd12-467f-abbc-27ad5abfc6fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_clip_eq
import Theorems.Thm_ClauseBound_Alg_CertLevel_fold_clip
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution (P : PiecesF) (b : U) (Kup lam B : ℕ) (sched : List Step) :
    needCut P (Kup + (sched.map Step.K).sum) b Kup lam B sched = needC P b Kup lam B sched := by
  have h0 : ∀ st, cap (List.replicate (100 * (b.length + 2)) ()) (none : Option NState) (some ((List.replicate lam (), B), (1, 1), (Kup, 0))) = some st →
      st.2.2.1 ≤ Kup + (sched.map Step.K).sum := by
    intro st hst
    unfold cap at hst
    split_ifs at hst
    · cases hst
      exact Nat.le_add_right _ _
  obtain ⟨h1, h2⟩ := fold_clip (needStep P) (fun _ _ => rfl) (List.replicate (100 * (b.length + 2)) ()) (Kup + (sched.map Step.K).sum) sched _
    (fun s hs => (List.le_sum_of_mem (List.mem_map_of_mem hs)).trans (Nat.le_add_left _ _)) h0
  unfold needCut needC
  rw [h1]
  cases h : sched.foldl (fun o s => cap (List.replicate (100 * (b.length + 2)) ()) none (o.map fun st => needStep P st s))
      (cap (List.replicate (100 * (b.length + 2)) ()) none (some ((List.replicate lam (), B), (1, 1), (Kup, 0)))) with
  | none => rfl
  | some st => rw [Option.bind_some, Option.bind_some, clip_eq (h2 st h)]
end ClauseBound.Alg.CertLevel

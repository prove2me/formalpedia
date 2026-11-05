-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.fold_clip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:49.842493+00:00
-- url     : https://prove2.me/submissions/dc9b0458-197b-4aeb-a9ab-006a70785c1c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_clip_eq
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution (f : NState → Step → NState) (hf : ∀ st s, (f st s).2.2.1 = s.K) (c : U) (M : ℕ) :
    ∀ (l : List Step) (o : Option NState), (∀ s ∈ l, s.K ≤ M) → (∀ st, o = some st → st.2.2.1 ≤ M) →
      l.foldl (fun o s => cap c none (o.map fun st => f (clip M st) s)) o = l.foldl (fun o s => cap c none (o.map fun st => f st s)) o ∧
        ∀ st, l.foldl (fun o s => cap c none (o.map fun st => f st s)) o = some st → st.2.2.1 ≤ M := by
  intro l
  induction l with
  | nil => intro o _ ho; exact ⟨rfl, ho⟩
  | cons s l ih =>
    intro o hl ho
    have h1 : (o.map fun st => f (clip M st) s) = o.map fun st => f st s := by
      cases o with
      | none => rfl
      | some st => rw [Option.map_some, Option.map_some, clip_eq (ho st rfl)]
    have h2 : ∀ st, cap c none (o.map fun st => f st s) = some st → st.2.2.1 ≤ M := by
      intro st hst
      unfold cap at hst
      split_ifs at hst
      · obtain ⟨st', -, rfl⟩ := Option.map_eq_some_iff.1 hst
        rw [hf]
        exact hl s (by simp)
    rw [List.foldl_cons, List.foldl_cons, h1]
    exact ih _ (fun s' hs' => hl s' (by simp [hs'])) h2
end ClauseBound.Alg.CertLevel

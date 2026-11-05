-- Prove2me | solution 1 for ClauseBound.Inst.Half.Par.par_of_cst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:34:29.002602+00:00
-- url     : https://prove2.me/submissions/eeda609b-5715-48ec-9738-ee7dbd6b52d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar
import Theorems.Thm_ClauseBound_Inst_Half_Par_abs_sOf_le
import Theorems.Thm_ClauseBound_Inst_Half_Par_cap_add_cap_le
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par
namespace ClauseBound.Inst.Half.Par
theorem _root_.solution (hS : StSpec) {c₀ c : ℕ} (hC : ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam) : ClauseBound.Gen.Par (halfF c₀ c) (1 / Real.sqrt 2) c where
  spec := fun h' lam hl => hS c₀ c lam h' hl (hC lam hl)
  caps := fun h' lam hl => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.range ((halfF c₀ c).cnt h' lam))
      (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero (4 * hF c₀ lam)))
      fun i => (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i
    have h1 : capSum (halfF c₀ c) h' lam = (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i := hi
    rw [h1]
    refine le_trans ?_ ((hC lam hl).caps (sOf (hOf lam) i) (abs_sOf_le _ _)).2.2
    exact_mod_cast cap_add_cap_le c h' i (hC lam hl).h_le
  cnt := fun h' lam hl => by
    change 4 * hF c₀ lam + 1 ≤ _
    rw [hF_eq (hC lam hl).h_le]
    exact (hC lam hl).cnt
  bits := fun _ _ _ => le_rfl
  d := fun h' lam hl => by
    change factN (hF c₀ lam) < _
    rw [hF_eq (hC lam hl).h_le, factN_eq]
    exact (hC lam hl).fact
  need := fun _ _ _ => le_rfl
  m_le := le_rfl
end ClauseBound.Inst.Half.Par

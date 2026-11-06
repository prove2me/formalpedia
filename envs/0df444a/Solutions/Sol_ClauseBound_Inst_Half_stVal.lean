-- Prove2me | solution 1 for ClauseBound.Inst.Half.stVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:29:07.961765+00:00
-- url     : https://prove2.me/submissions/72cc6094-14d6-42e2-a0f8-236683acd567

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_ClauseBound_Inst_Half_partH_eq
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq
import Theorems.Thm_ClauseBound_Part_two_le_hOf
import Theorems.Thm_ClauseBound_Part_two_pow_le_p_hOf
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open Val
namespace ClauseBound.Inst.Half
theorem _root_.solution (hT : StTopF) (hB : StBotF) (hE : StEnc) : StVal := by
  intro c₀ lam pad _ hc hp tr top h' i a b θ
  have hh : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hc
  obtain ⟨e1, -⟩ := hE lam (ClauseBound.Part.hOf lam) ((by norm_num : 1 ≤ 2).trans (ClauseBound.Part.two_le_hOf lam)) (ClauseBound.Part.two_pow_le_p_hOf lam)
  have h := partH_eq hT hB (c₀ := c₀) (lam := lam) (pad := pad) (by rw [hh]; exact hp) tr top h' i a b θ
    (by rw [hh]; exact ⟨(e1 a).2.2, (e1 a).2.1⟩) (by rw [hh]; exact ⟨(e1 b).2.2, (e1 b).2.1⟩)
  rw [hh] at h
  exact h
end ClauseBound.Inst.Half

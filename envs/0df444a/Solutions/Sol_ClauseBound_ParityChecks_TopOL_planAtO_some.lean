-- Prove2me | solution 1 for ClauseBound.ParityChecks.TopOL.planAtO_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:46.903191+00:00
-- url     : https://prove2.me/submissions/789f3c9e-ed4a-4ba7-95c6-781b41d1614d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace ClauseBound.ParityChecks.TopOL
theorem _root_.solution {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {c n₀ k n s v : ℕ} {i : Idx} (h : planAtO S c n₀ k n i s = some v) :
    (s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) ∧ v = needO S k i n s := by
  unfold planAtO at h
  split_ifs at h with hc
  obtain ⟨v', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h2 with hc2
  obtain ⟨u, h3, h4⟩ := Option.map_eq_some_iff.1 h1
  have hu := hS.needC_eq _ _ _ h3
  refine ⟨hc, ?_⟩
  rw [← Option.some.inj h2, ← h4, hu]
  rfl
end ClauseBound.ParityChecks.TopOL

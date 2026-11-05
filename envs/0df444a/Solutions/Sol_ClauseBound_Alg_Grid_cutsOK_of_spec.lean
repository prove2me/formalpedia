-- Prove2me | solution 1 for ClauseBound.Alg.Grid.cutsOK_of_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:08:19.968718+00:00
-- url     : https://prove2.me/submissions/07d35aee-73cf-4900-9bfc-03fdb509e3cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_ClauseBound_Alg_Grid
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
import Theorems.Thm_PaddedDescent_F_RebalF_cap_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Grid
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.Grid
theorem _root_.solution {P : PiecesF} {pad : U} {h ℓ : ℕ} (hS : P.Spec h ℓ) (hpad : 2 ^ P.need h ℓ ≤ pad.length) :
    ∃ A : ℕ → Pieces.Four ℓ, (∀ x y u v, ∑ i ∈ range (P.cnt h ℓ), A i x y u v = P.d h ℓ * Pieces.cross x y u v) ∧
      CutsOK P pad h ℓ A := by
  obtain ⟨A, hsum, habs, hfac⟩ := hS.ex
  refine ⟨A, hsum, hS.cnt_pos, hS.m_pos, fun tr i hi => ?_, fun tr i hi => hS.cap_le tr i hi, habs,
    fun tr i hi x y θ => ((hfac pad hpad i hi).2.2 tr x y θ).1, fun tr i hi x y θ => ((hfac pad hpad i hi).2.2 tr x y θ).2⟩
  cases tr
  · exact (hfac pad hpad i hi).1
  · exact fun x y u v => (hfac pad hpad i hi).2.1 x u y v
end ClauseBound.Alg.Grid

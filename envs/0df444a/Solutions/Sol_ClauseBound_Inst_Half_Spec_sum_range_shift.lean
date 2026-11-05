-- Prove2me | solution 1 for ClauseBound.Inst.Half.Spec.sum_range_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:31.924179+00:00
-- url     : https://prove2.me/submissions/3d4690f1-9813-49ad-8171-df09b7e7f676

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfSpec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Spec
namespace ClauseBound.Inst.Half.Spec
theorem _root_.solution (h : ℕ) (f : ℤ → ℤ) : ∑ i ∈ range (4 * h + 1), f ((i : ℤ) - 2 * h) = ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), f s := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ℤ) - 2 * h) (fun s => (s + 2 * h).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_range] at hi
    rw [mem_Icc]
    omega
  · intro s hs
    rw [mem_Icc] at hs
    rw [mem_range]
    omega
  · intro i _
    omega
  · intro s hs
    rw [mem_Icc] at hs
    omega
  · intro i _
    rfl
end ClauseBound.Inst.Half.Spec

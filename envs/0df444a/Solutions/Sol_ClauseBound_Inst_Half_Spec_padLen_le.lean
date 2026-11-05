-- Prove2me | solution 1 for ClauseBound.Inst.Half.Spec.padLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:30.145948+00:00
-- url     : https://prove2.me/submissions/1047887f-c675-48b0-b83b-8953b3cf5929

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfSpec
import Theorems.Thm_ClauseBound_Inst_Half_Spec_deltaF_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Spec
namespace ClauseBound.Inst.Half.Spec
theorem _root_.solution {c₀ c lam : ℕ} (hC : Cst c₀ c lam) : padLen (ClauseBound.Part.hOf lam) ≤ 2 ^ (c * lam) := by
  rw [padLen, deltaF_eq]
  exact hC.pad
end ClauseBound.Inst.Half.Spec

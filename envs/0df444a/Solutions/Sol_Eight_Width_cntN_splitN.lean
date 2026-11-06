-- Prove2me | solution 1 for Eight.Width.cntN_splitN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:04.071228+00:00
-- url     : https://prove2.me/submissions/0e04d6a8-92f5-4f61-b4d7-0f0f41e79434

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
import Theorems.Thm_Eight_Width_numFresh_toN
import Theorems.Thm_Eight_Width_toN_widthReduce
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_Eight_Width_numSat_widthReduce


set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat
namespace Eight.Width
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) :
    cntN (n + numFresh (Decode.toN φ)) (splitN n (Decode.toN φ)) = cntN n (Decode.toN φ) := by
  rw [← toN_widthReduce, numFresh_toN, stCntToN, stCntToN, numSat_widthReduce]
end Eight.Width

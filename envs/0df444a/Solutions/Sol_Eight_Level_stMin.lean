-- Prove2me | solution 1 for Eight.Level.stMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:23:09.510493+00:00
-- url     : https://prove2.me/submissions/7f0779a2-a050-4188-82c4-5e96c5b98b99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_Level_Min
import Theorems.Thm_Eight_Level_eqMinTotal_words
import Theorems.Thm_P2M_Eight_Level_U_netOf__16d6ae6630a8


set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg
namespace Eight.Level
theorem _root_.solution : StMin := fun g lam y hlam => by
  rw [← U_netOfι g false lam y fun _ _ => 0, ← U_netOfι g true lam y fun _ _ => 0]
  exact eqMinTotal_words hlam g y _
end Eight.Level

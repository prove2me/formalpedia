-- Prove2me | solution 1 for ClauseBound.Part.Upper.cHR_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:23:33.268725+00:00
-- url     : https://prove2.me/submissions/9afe6cbf-bf35-41a3-8781-eab06fdbdb2b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper
namespace ClauseBound.Part.Upper
theorem _root_.solution : 0 < cHR := by
  unfold cHR
  positivity
end ClauseBound.Part.Upper

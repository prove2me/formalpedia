-- Prove2me | solution 1 for FromPrinted.Consequences.stVerifier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:22:36.641257+00:00
-- url     : https://prove2.me/submissions/deede813-8ea7-4db0-b8a3-ff0143ea4063

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
import Definitions.Def_FromPrinted_Verifier
import Theorems.Thm_Eight_ViaGrouping_verifier_polyTimeSteps
import Theorems.Thm_Eight_ViaGrouping_verifier_recognizes
import Theorems.Thm_FromPrinted_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_stSATsplit


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences
namespace FromPrinted.Consequences
theorem _root_.solution : StVerifier := by
  intro k hk δ hδ
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hc⟩ := FromPrinted.SplitSat.stSATsplit k hk δ hδ
  exact ⟨τ, ℓ₃, τ₃, c, hp, hc, verifier_polyTimeSteps hp, verifier_recognizes hc⟩
end FromPrinted.Consequences

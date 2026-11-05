-- Prove2me | solution 1 for ClauseBound.ParityChecks.stepTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:25:56.65921+00:00
-- url     : https://prove2.me/submissions/a04ebfab-57f7-4ece-90b3-2e1b61b9ad41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Definitions.Def_ClauseBound_ParityChecks_Start
import Definitions.Def_ClauseBound_ParityChecks_Structure
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_ChoiceByPotential
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_le
import Theorems.Thm_ClauseBound_ParityChecks_Approx_approx
import Theorems.Thm_ClauseBound_ParityChecks_Approx_compute
import Theorems.Thm_ClauseBound_ParityChecks_Martingale_martingale
import Theorems.Thm_ClauseBound_ParityChecks_Start_boundary
import Theorems.Thm_ClauseBound_ParityChecks_Start_five_eighths
import Theorems.Thm_ClauseBound_ParityChecks_Start_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Start_start
import Theorems.Thm_ClauseBound_ParityChecks_Structure_final
import Theorems.Thm_ClauseBound_ParityChecks_Structure_structure_


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks
theorem _root_.solution : _root_.ParityChecks.ChoiceByPotential where
  nonneg := Start.nonneg
  five_eighths := Start.five_eighths
  start := Start.start
  martingale := Martingale.martingale
  boundary := Start.boundary
  structure_ := fun X E _ _ _ V nb r j Λ D hnb hE hs hU => Structure.structure_ V nb r j Λ D (Start.nonneg X E V nb r j Λ D hnb) hnb hE hs hU
  final := fun X E _ _ _ V nb r Λ hnb hs hU => Structure.final V nb r Λ (Start.nonneg X E V nb r (r - 1) Λ ∅ hnb) hs hU
  approx := fun _ _ _ _ _ => Approx.approx
  compute := fun _ _ _ _ _ => Approx.compute
  abs_le := fun _ _ _ _ _ => Approx.abs_le
end ClauseBound.ParityChecks

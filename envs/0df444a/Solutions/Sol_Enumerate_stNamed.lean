-- Prove2me | solution 1 for Enumerate.stNamed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:21.852174+00:00
-- url     : https://prove2.me/submissions/774a3c3e-b5eb-4f41-a991-05f26d5228dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_SparsificationLemma_Mach_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Enumerate_Named
import Theorems.Thm_Enumerate_stNamedOf
import Theorems.Thm_Enumerate_stEnumeratesTau
import Theorems.Thm_Enumerate_stProducedIsList
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_SparsificationLemma_Mach_prints
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
namespace Enumerate
theorem _root_.solution : StNamed := stNamedOf prints stProducedIsList stEnumeratesTau
end Enumerate

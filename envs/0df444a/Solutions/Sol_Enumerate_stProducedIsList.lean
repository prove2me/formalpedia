-- Prove2me | solution 1 for Enumerate.stProducedIsList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:01:16.176571+00:00
-- url     : https://prove2.me/submissions/944404d7-1a3a-4f87-b2a3-cda1df555232

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_Enumerate_Enumeration
import Theorems.Thm_SparsificationLemma_stOutputsSame


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo
namespace Enumerate
theorem _root_.solution : StProducedIsList := fun τ n φ => stOutputsSame (thetaU τ) 3 (bsumU τ 3 * n) n φ
end Enumerate

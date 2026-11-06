-- Prove2me | solution 1 for Enumerate.sat_iff_of_exactlyOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:11.530921+00:00
-- url     : https://prove2.me/submissions/49b4436b-b360-4c40-8b0c-ef123a312bf9

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

set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo
namespace Enumerate
theorem _root_.solution {φ : PFml} {L : List PFml} (h : ∀ b, ExactlyOne b φ L) : (∃ b, SparsificationLemma.Sat b φ) ↔ ∃ Φ ∈ L, ∃ b, SparsificationLemma.Sat b Φ := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨i, hi, -⟩ := (h b).1 hb
    exact ⟨L.get i, List.get_mem _ _, b, hi⟩
  · rintro ⟨Φ, hΦ, b, hb⟩
    by_contra hno
    exact (h b).2 (fun hs => hno ⟨b, hs⟩) Φ hΦ hb
end Enumerate

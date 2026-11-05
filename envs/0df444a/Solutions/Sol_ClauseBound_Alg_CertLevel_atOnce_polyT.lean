-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.atOnce_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:59.5916+00:00
-- url     : https://prove2.me/submissions/ee915ad6-aebb-4f5b-ba7e-7b8b0b54726d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_ClauseBound_Alg_CertLevel_thin_polyT
import Theorems.Thm_ClauseBound_Alg_CertLevel_colSide_polyT
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
variable (hP : P.Keeps)
include hP
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution {s : α → Step} {l : α → U} {y : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => ((s x).thin && colSide P (s x) (l x).length (y x)) :=
  PolyT.and' (thin_polyT hs) (colSide_polyT hP hs hl hy)
end ClauseBound.Alg.CertLevel

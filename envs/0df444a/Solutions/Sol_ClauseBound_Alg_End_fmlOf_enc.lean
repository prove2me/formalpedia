-- Prove2me | solution 1 for ClauseBound.Alg.End.fmlOf_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:14:50.46299+00:00
-- url     : https://prove2.me/submissions/1048a4a9-04fd-4564-8e87-b1d9ca2c7cd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_ClauseBound_Alg_End_kOf_enc
import Theorems.Thm_ClauseBound_Alg_End_restOf_enc
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (hφ : ∀ C ∈ φ, C.length ≤ k) :
    fmlOf (SatM.enc k φ) = (List.replicate n (), Decode.toN φ) := by
  rw [fmlOf, kOf_enc, restOf_enc, List.length_replicate]
  exact stDecU k n φ hk hφ
end ClauseBound.Alg.End

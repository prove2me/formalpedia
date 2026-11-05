-- Prove2me | solution 1 for ClauseBound.Alg.CertLevel.clip_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:23:55.308849+00:00
-- url     : https://prove2.me/submissions/ca91562f-0293-4929-829b-f1cdc04c92ae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
namespace ClauseBound.Alg.CertLevel
theorem _root_.solution {M : ℕ} {st : NState} (h : st.2.2.1 ≤ M) : clip M st = st := by
  unfold clip
  rw [min_eq_left h]
end ClauseBound.Alg.CertLevel

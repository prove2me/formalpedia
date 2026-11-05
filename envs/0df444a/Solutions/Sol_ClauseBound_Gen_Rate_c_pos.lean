-- Prove2me | solution 1 for ClauseBound.Gen.Rate.c_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:16:46.96919+00:00
-- url     : https://prove2.me/submissions/a2131142-0ead-45e3-a08c-1e94d261d677

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Rate

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace ClauseBound.Gen.Rate
theorem _root_.solution (hP : Par P ρ c) : 1 ≤ c := le_trans (hP.spec 0 1 le_rfl).m_pos hP.m_le
end ClauseBound.Gen.Rate

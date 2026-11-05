-- Prove2me | solution 1 for CountKSat.EndLemmas.CountsTM.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:38.201357+00:00
-- url     : https://prove2.me/submissions/999fd616-b1b7-4603-b65b-48da3f9796ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_CountKSat_EndLemmas

set_option autoImplicit false
section
open CountKSat CountKSat.EndLemmas
open Turing SatK
open scoped NNReal ENNReal
namespace CountKSat.EndLemmas
namespace CountsTM
theorem _root_.solution {k : ℕ} {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : CountsTM k M t) (ht : ∀ n, t n ≤ t' n) :
    CountsTM k M t' := fun n φ hφ => by
  obtain ⟨e⟩ := h n φ hφ
  exact ⟨⟨e.toEvalsTo, e.steps_le_m.trans (ht n)⟩⟩
end CountsTM
end CountKSat.EndLemmas

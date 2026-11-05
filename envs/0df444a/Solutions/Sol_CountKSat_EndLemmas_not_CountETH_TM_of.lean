-- Prove2me | solution 1 for CountKSat.EndLemmas.not_CountETH_TM_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:36.569921+00:00
-- url     : https://prove2.me/submissions/0b87e27e-35ca-4fe6-bb63-a93876d23a0d

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
theorem _root_.solution (h : ∀ δ : ℝ≥0, 0 < δ → CountInTimeTM 3 δ) : ¬ CountETH_TM := fun ⟨δ, h0, hn⟩ => hn (h δ h0)
end CountKSat.EndLemmas

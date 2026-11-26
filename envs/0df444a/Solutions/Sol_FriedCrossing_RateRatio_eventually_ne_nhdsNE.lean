-- Prove2me | solution 1 for FriedCrossing.RateRatio.eventually_ne_nhdsNE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:38:43.26486+00:00
-- url     : https://prove2.me/submissions/24fdfc77-4671-45da-a9b1-f2b4cd7d4c57

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution (σ : ℝ) : ∀ᶠ τ in 𝓝[≠] σ, τ ≠ σ :=
  eventually_nhdsWithin_of_forall fun _ h => h
end FriedCrossing.RateRatio

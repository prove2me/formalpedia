-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.minFac_prime_of_pp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:26.743367+00:00
-- url     : https://prove2.me/submissions/7d932be8-1580-4bda-867c-870eecd48563

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
theorem _root_.solution {n : ℕ} (h : IsPrimePow n) : n.minFac.Prime := Nat.minFac_prime h.ne_one
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs

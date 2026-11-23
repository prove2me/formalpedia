-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.soutPart_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:19.488799+00:00
-- url     : https://prove2.me/submissions/31d033df-aee1-4385-8b81-bafc3067abda

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac

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
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

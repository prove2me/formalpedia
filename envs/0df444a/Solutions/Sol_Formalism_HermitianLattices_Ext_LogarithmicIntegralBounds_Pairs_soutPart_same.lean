-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_same
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:55.324875+00:00
-- url     : https://prove2.me/submissions/91a74a50-f91e-4734-896f-a791db5e4601

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_prime_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePow_data

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
theorem _root_.solution {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac = n'.minFac) :
    soutPart m₀ (n * n') = 1 ∨ soutPart m₀ (n * n') = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p = q := hm.symm.trans (he.trans hm')
  subst hpq
  rw [← pow_add, soutPart_prime_pow m₀ p (k + k') hp (by omega), hm]
  split_ifs <;> simp
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs

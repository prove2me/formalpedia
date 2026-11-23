-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.gW_eq_of_tPart_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:10.536804+00:00
-- url     : https://prove2.me/submissions/8f048c21-9a76-4003-a0f8-a891b231a94a

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
theorem _root_.solution {c : ℕ → ℝ} {m₀ n : ℕ} (h : IsPrimePow n) (ht : tPart m₀ n = 1) : gW c m₀ n = c n := by
  have hcond : Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ := by
    unfold tPart at ht
    split_ifs at ht with h1
    · exact h1
    · exact absurd ht (Nat.minFac_prime h.ne_one).one_lt.ne'
  unfold gW
  rw [if_pos ⟨h, hcond⟩]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs

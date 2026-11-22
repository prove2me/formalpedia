-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.aW_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:18.632752+00:00
-- url     : https://prove2.me/submissions/b16be087-e34f-4ef4-a34d-4246049c9c33

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
theorem _root_.solution {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (p n : ℕ) : 0 ≤ aW c p n := by
  unfold aW
  split_ifs
  · exact hc n
  · exact le_refl 0
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs

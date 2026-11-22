-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:45.244791+00:00
-- url     : https://prove2.me/submissions/9c751177-92c2-4d53-ac23-175aba4cc309

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth

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
theorem _root_.solution {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]
  have h' : a % s = b % s := h
  rw [← Int.natCast_mod, ← Int.natCast_mod, h']
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

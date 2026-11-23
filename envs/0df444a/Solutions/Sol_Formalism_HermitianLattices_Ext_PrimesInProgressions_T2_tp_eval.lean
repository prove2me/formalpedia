-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:20.408868+00:00
-- url     : https://prove2.me/submissions/ecadfae3-ac5b-4dd4-9b1c-34f027f12ecf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (n : ℕ) (z : Fin n → ℂ) (x : ℂ) : (tp n z).eval x = ∏ i, (x - z i) := by
  simp [tp, eval_prod]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

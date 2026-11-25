-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_phi_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:45.379069+00:00
-- url     : https://prove2.me/submissions/eefda893-3f0a-448e-a67a-feb9854a5b8a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := by
  have h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have h2 := h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 =
      (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [Complex.cpow_one, ← Complex.ofReal_log hy.le]
    ring
  exact h2.congr_deriv e
end Formalism.HermitianLattices.Ext.PrimesInProgressions

-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.excTerm_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:33.342865+00:00
-- url     : https://prove2.me/submissions/52519ed2-f181-4d9c-bcea-5611024455dc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (x β : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ (β : ℂ) / (β : ℂ) = ((x ^ β / β : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_cpow hx]
end Formalism.HermitianLattices.Ext.SupplyAP

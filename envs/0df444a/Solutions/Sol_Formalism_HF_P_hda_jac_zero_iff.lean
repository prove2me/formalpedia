-- Prove2me | solution 1 for Formalism.HF.P.hda_jac_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:01.040071+00:00
-- url     : https://prove2.me/submissions/55479c34-21e4-41e1-9087-85007a5fb91b

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = 0 ↔ p ∣ m := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff, Int.cast_natCast,
    ZMod.natCast_eq_zero_iff]
end Formalism.HF.P

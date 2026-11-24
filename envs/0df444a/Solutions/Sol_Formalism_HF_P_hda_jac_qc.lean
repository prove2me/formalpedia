-- Prove2me | solution 1 for Formalism.HF.P.hda_jac_qc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:00.923206+00:00
-- url     : https://prove2.me/submissions/fdb8676e-fa4a-4b41-be58-1bb098d835ec

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
    jacobiSym (m : ℤ) p = quadraticChar (ZMod p) (m : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  unfold legendreSym
  rw [Int.cast_natCast]
end Formalism.HF.P

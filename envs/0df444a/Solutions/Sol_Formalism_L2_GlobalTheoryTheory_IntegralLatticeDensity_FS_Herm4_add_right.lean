-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:14.167435+00:00
-- url     : https://prove2.me/submissions/5ffb6c0c-76d8-40f2-9b6c-5d49f32e53f5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) (x y z : V) : h x (y + z) = h x y + h x z := by
  rw [H.symm (y + z) x, H.add_left, map_add, ← H.symm, ← H.symm]
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

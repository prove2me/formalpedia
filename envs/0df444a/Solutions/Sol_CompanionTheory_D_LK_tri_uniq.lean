-- Prove2me | solution 1 for CompanionTheory.D.LK.tri_uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:05.139943+00:00
-- url     : https://prove2.me/submissions/8974ecef-8732-44f8-9eef-9da1d854db47

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.LK
theorem _root_.solution {i j k k' : Pos n} (h : Tri ε i j k) (h' : Tri ε i j k') : k = k' :=
  Subtype.ext (Prod.ext (h.2.2.2.1.trans h'.2.2.2.1.symm) (h.2.2.2.2.trans h'.2.2.2.2.symm))
end CompanionTheory.D.LK

-- Prove2me | solution 1 for Formalism.L2.Pj.betaAt_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:37.510107+00:00
-- url     : https://prove2.me/submissions/a345f5a4-7384-48fc-ac99-edda4aa0f042

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {R : Type} [CommRing R] [IsDomain R]
namespace Formalism.L2.Pj
theorem _root_.solution (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) :
    betaAt D f p a b = betaAt D f p b a := by
  unfold betaAt
  rw [add_comm a b]
  ring
end Formalism.L2.Pj

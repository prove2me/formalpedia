-- Prove2me | solution 1 for F6RotationSupport.supports_disjoint_of_incomparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:38:22.186167+00:00
-- url     : https://prove2.me/submissions/a9cf146c-fc7a-487e-8e38-99ca7a4d3c83

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {rho sigma : R} (hinc : F6ConvexWindow.IncRel rho sigma) :
    Disjoint (supp rho) (supp sigma) := by
  apply Finset.disjoint_left.mpr
  intro m hrho hsigma
  exact (HSHARE rho sigma ⟨m, mem_inter.mpr ⟨hrho, hsigma⟩⟩).elim hinc.1 hinc.2
end F6RotationSupport

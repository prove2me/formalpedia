-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbSum.card_stab_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:45.362044+00:00
-- url     : https://prove2.me/submissions/b9ff8bd6-ce98-4358-a57d-857ff24ee127

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbSum
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
namespace Formalism.HermitianLattices.Ext.L3.OrbSum
theorem _root_.solution (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
end Formalism.HermitianLattices.Ext.L3.OrbSum

-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubicFlow.der_gE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:23.072046+00:00
-- url     : https://prove2.me/submissions/4a6ca306-a50a-4d38-851e-24497b872424

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubicFlow
open QuadraticFlow
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A.CubicFlow
theorem _root_.solution {D : A → A} (hD : IsDer D) {W : WeierstrassCurve A} (hC : ConstCurve D W) (z v : A) :
    D (gE W z v) = fuAt W z v * D z - fwAt W z v * D v := by
  obtain ⟨hadd, hmul⟩ := hD
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  have hsub : ∀ a b, D (a - b) = D a - D b := by
    intro a b
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  have hp2 : ∀ a, D (a ^ 2) = 2 * a * D a := fun a => by rw [sq, hmul]; ring
  have hp3 : ∀ a, D (a ^ 3) = 3 * a ^ 2 * D a := fun a => by
    rw [show a ^ 3 = a * a ^ 2 by ring, hmul, hp2]; ring
  unfold gE fuAt fwAt
  simp only [hsub, hadd, hmul, hp2, hp3, c1, c2, c3, c4, c6]
  ring
end Formalism.L2.Th1.A.CubicFlow

-- Prove2me | solution 1 for ErdosPosa.reach_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:20:06.509142+00:00
-- url     : https://prove2.me/submissions/feee9299-cb76-431d-93a4-f4ff54064638

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {W : Type*} {G1 : SimpleGraph V} {G2 : SimpleGraph W} (f : V → W)
    (h : ∀ a b, G1.Adj a b → G2.Reachable (f a) (f b)) {a b : V} (hab : G1.Reachable a b) :
    G2.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (h _ _ hadj).trans ih
end ErdosPosa

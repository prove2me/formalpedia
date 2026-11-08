-- Prove2me | solution 1 for ConicBlackwell.lemma_3_2_statement_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:13:51.226398+00:00
-- url     : https://prove2.me/submissions/b4dc244c-6b59-4a21-9821-553bd1f01f6e

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace Aux_CB325

theorem polar_add {n : ℕ} (C : Set (E (n + 1))) (a b : E (n + 1))
    (ha : a ∈ polar C) (hb : b ∈ polar C) : a + b ∈ polar C := by
  intro x hx
  rw [inner_add_left]
  have := ha x hx
  have := hb x hx
  linarith

end Aux_CB325

open Aux_CB325 in
theorem solution {n : ℕ} (C : Set (E (n + 1)))
    (hC : MoreauProx.Decomposition.IsClosedConvexCone C) :
    (∀ x x' y y' : E (n + 1), y - x ∈ polar C → y' - x' ∈ polar C →
        (y + y') - (x + x') ∈ polar C) ∧
      (∀ x y x' : E (n + 1), x' ∈ polar C → y - (x + x') ∈ polar C → y - x ∈ polar C) := by
  refine ⟨fun x x' y y' h1 h2 => ?_, fun x y x' h1 h2 => ?_⟩
  · have e : (y + y') - (x + x') = (y - x) + (y' - x') := by abel
    rw [e]; exact polar_add C _ _ h1 h2
  · have e : y - x = (y - (x + x')) + x' := by abel
    rw [e]; exact polar_add C _ _ h2 h1

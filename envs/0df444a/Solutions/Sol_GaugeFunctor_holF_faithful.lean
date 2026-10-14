-- Prove2me | solution 1 for GaugeFunctor.holF_faithful
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-11T19:43:14.73377+00:00
-- url     : https://prove2.me/submissions/a08fd605-2ba0-4928-8307-61afe58f11e6

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

theorem hff_main (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Faithful := by
  refine ⟨fun {A B} {g g'} hgg => ?_⟩
  have hx : g.1 x = g'.1 x := congrArg Subtype.val hgg
  apply Subtype.ext
  funext y
  obtain ⟨w, hw⟩ := hX y
  have h1 := hol_gaugeAct (X := X) (G := G) g.1 A.conn w x y hw
  have h2 := hol_gaugeAct (X := X) (G := G) g'.1 A.conn w x y hw
  rw [g.2] at h1
  rw [g'.2, ← hx, h1] at h2
  have := mul_left_cancel h2
  exact inv_injective this

end GaugeFunctor

open GaugeFunctor

theorem solution (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Faithful := hff_main X G x hX

-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_28
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:40:34.430587+00:00
-- url     : https://prove2.me/submissions/57e54c8f-e2f2-4d75-825a-68a577f2cb06

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    (underlying K T).Faithful := by
  constructor
  intro X Y f g h
  have hT' : f.hom.app (op T) = g.hom.app (op T) := h
  ext E φ
  apply Y.property.2 E.unop
  funext d
  show Y.obj.map d.op (f.hom.app E φ) = Y.obj.map d.op (g.hom.app E φ)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact CategoryTheory.congr_fun hT' _

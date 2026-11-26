-- Prove2me | solution 1 for CurveRestrictTotAgrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:35.011377+00:00
-- url     : https://prove2.me/submissions/04a6a968-2c33-4ea0-ab09-04be8bbe3084

import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurveRestrictTotAgrees

set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) :
    curveRestrictTot γ a b = curveRestrict γ a b ha hab hb := by
-- BODY
  have curve_ext : ∀ {c1 c2 : Curve E}, c1.len = c2.len → c1.toFun = c2.toFun → c1 = c2 := by
    intro c1 c2 hlen htoFun
    cases c1; cases c2; subst hlen; subst htoFun; rfl
  have hb0 : 0 ≤ b := ha.trans hab
  have h1 : min (max a 0) γ.len = a := by
    rw [max_eq_left ha, min_eq_left (hab.trans hb)]
  have h2 : max a (min (max b 0) γ.len) = b := by
    rw [max_eq_left hb0, min_eq_left hb, max_eq_right hab]
  apply curve_ext
  · show max (min (max a 0) γ.len) (min (max b 0) γ.len) - min (max a 0) γ.len = b - a
    rw [h1, h2]
  · funext u
    show γ.toFun (min (max a 0) γ.len +
        min (max (min (max a 0) γ.len) (min (max b 0) γ.len) - min (max a 0) γ.len) (max 0 u))
      = γ.toFun (a + min (b - a) (max 0 u))
    rw [h1, h2]

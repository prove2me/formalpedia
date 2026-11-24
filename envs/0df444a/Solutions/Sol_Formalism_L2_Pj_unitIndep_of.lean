-- Prove2me | solution 1 for Formalism.L2.Pj.unitIndep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:03.978495+00:00
-- url     : https://prove2.me/submissions/ffcbeb45-f99b-4024-94cd-cf8431cfa608

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Theorems.Thm_Formalism_L2_Pj_valV_wchar_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Open
variable (Xo : Moduli Dw l) (c : Coeff l)
end Open
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
private theorem vV_mul_lemma {T : CDVR} {w x : T.Fr} (hu : valV T.V w = 1) (hx : x ≠ 0) :
    vV T.V (w * x) = vV T.V x := by
  unfold vV
  rw [map_mul, hu, one_mul]
end Proofs
end Formalism.L2.Pj
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (hW : WtField Xo c) (hU : IntDiagUnit Xo c) : UnitIndep Xo c := by
  intro a n f hf T io y y' t hb e
  letI := io.toAlgebra
  have hw := hW a n f hf T.Fr t y.1 y'.1 y.2.1 y'.2.1 hb
  have hu := valV_wchar_eq_one (ex Dw a n) t (hU T io y y' t hb)
  unfold nval evI
  rw [hw]
  generalize evR Xo c f y.1 = x at *
  have hne : wchar (ex Dw a n) t ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact zero_ne_one hu
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (mul_ne_zero hne hx), if_neg hx, vV_mul_lemma hu hx]
end Formalism.L2.Pj

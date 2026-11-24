-- Prove2me | solution 1 for Formalism.L2.Th1.A.der_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:39.491335+00:00
-- url     : https://prove2.me/submissions/e92e010e-11d2-4657-993e-dc17d6bbb4cd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Theorems.Thm_Formalism_L2_Th1_A_der_mul
import Theorems.Thm_Formalism_L2_Th1_A_der_inv
import Theorems.Thm_Formalism_L2_Th1_A_chord_rel

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
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A
theorem _root_.solution (W : WeierstrassCurve A) (d : Derivation ℤ A A) {x y xP yP t : A}
    (hE : W.toAffine.Equation x y) (hx : d x = 2 * y + W.a₁ * x + W.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hEP : W.toAffine.Equation xP yP) (hxP : d xP = 0) (hyP : d yP = 0)
    (ht : t * (x - xP) = 1) :
    d ((y - yP) * t) = x - W.toAffine.addX x xP ((y - yP) * t) := by
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, -⟩ := chord_rel hE' hEP' ht hL
  have hdt : d t = -t ^ 2 * d (x - xP) := der_inv d ht
  have hdxs : d (x - xP) = d x := by rw [map_sub, hxP, sub_zero]
  rw [der_mul, map_sub, hyP, sub_zero, hdt, hdxs, hx, hy]
  simp only [WeierstrassCurve.Affine.addX]
  linear_combination (x - (((y - yP) * t) ^ 2 + W.a₁ * ((y - yP) * t) - W.a₂ - x - xP)) * ht + t * hα
end Formalism.L2.Th1.A

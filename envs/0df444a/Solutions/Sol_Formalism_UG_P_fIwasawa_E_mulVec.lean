-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_E_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:10.375035+00:00
-- url     : https://prove2.me/submissions/931cf7c7-279d-4c35-8d79-312c13d9611b

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (e z : Fin n → L) (c : L) (w : Fin n → L) :
    fIwasawaE σ e z c *ᵥ w = w + fIwasawaH σ e w • z - fIwasawaH σ z w • e +
      (c * fIwasawaH σ e w) • e := by
  funext i
  simp only [fIwasawaE, fIwasawaH, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf
end Formalism.UG.P

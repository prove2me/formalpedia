-- Prove2me | solution 1 for Formalism.UG.P.map_polyAct_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:59.556187+00:00
-- url     : https://prove2.me/submissions/7fc54fa1-4cb9-499f-b053-bd3038490340

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (g : GL n O) (K : ℕ) :
    map (polyAct O n g).toRingHom
        ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = (∑ i, C (X i) *
          map C (∑ j, C (((g⁻¹ : GL n O) : Matrix n n O) j i) * X j) :
            MvPolynomial n (MvPolynomial n O)) ^ K := by
  rw [map_pow]
  congr 1
  simp only [map_sum, map_mul, map_C, map_X, polyAct, linSubst, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_X, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring
end Formalism.UG.P

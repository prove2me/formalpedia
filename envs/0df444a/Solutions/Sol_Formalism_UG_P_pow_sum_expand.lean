-- Prove2me | solution 1 for Formalism.UG.P.pow_sum_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:45.124+00:00
-- url     : https://prove2.me/submissions/6c917702-4801-4e0a-9b21-69def8e5c992

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
theorem _root_.solution (a b : n → MvPolynomial n O) (K : ℕ) :
    (∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          C ((Nat.multinomial Finset.univ β : MvPolynomial n O) * ∏ j, a j ^ β j) *
            map C (∏ j, b j ^ β j) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, map_mul, map_natCast]
  ring
end Formalism.UG.P

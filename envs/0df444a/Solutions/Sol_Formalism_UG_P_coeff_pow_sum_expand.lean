-- Prove2me | solution 1 for Formalism.UG.P.coeff_pow_sum_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:06.188677+00:00
-- url     : https://prove2.me/submissions/f3ef9c3c-fb73-49b8-bb56-fb5808a94a99

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Theorems.Thm_Formalism_UG_P_pow_sum_expand

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
theorem _root_.solution (a b : n → MvPolynomial n O) (K : ℕ) (α : n →₀ ℕ) :
    coeff α ((∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          (Nat.multinomial Finset.univ β : MvPolynomial n O) * (∏ j, a j ^ β j) *
            C (coeff α (∏ j, b j ^ β j)) := by
  rw [pow_sum_expand, coeff_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [coeff_C_mul, coeff_map]
end Formalism.UG.P

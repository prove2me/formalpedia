-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:05.491521+00:00
-- url     : https://prove2.me/submissions/45ce9481-51a4-4af0-9a5f-72d358fbadbf

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]
namespace Formalism.CyclotomicNorms.Sqf
theorem _root_.solution {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.2), zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm)) (by simp)]
  simp
end Formalism.CyclotomicNorms.Sqf

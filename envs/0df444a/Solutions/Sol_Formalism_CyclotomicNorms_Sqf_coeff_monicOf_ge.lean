-- Prove2me | solution 1 for Formalism.CyclotomicNorms.Sqf.coeff_monicOf_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:50.04803+00:00
-- url     : https://prove2.me/submissions/363d6611-b770-4e27-be65-6640efee038d

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
theorem _root_.solution {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by have := j.2; omega)), add_zero]
end Formalism.CyclotomicNorms.Sqf

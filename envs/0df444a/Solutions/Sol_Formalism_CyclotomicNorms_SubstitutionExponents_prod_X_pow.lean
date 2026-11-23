-- Prove2me | solution 1 for Formalism.CyclotomicNorms.SubstitutionExponents.prod_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:51.589729+00:00
-- url     : https://prove2.me/submissions/9d9144d8-7f99-49d6-be6f-ed056c84b825

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}
namespace Formalism.CyclotomicNorms.SubstitutionExponents
theorem _root_.solution {k : Type*} [CommRing k] (n : Fin r → ℕ) (d : Fin r →₀ ℕ) :
    (d.prod fun s e => ((PowerSeries.X : PowerSeries k) ^ n s) ^ e) =
      PowerSeries.X ^ weight n d := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [weight, mul_comm]
end Formalism.CyclotomicNorms.SubstitutionExponents

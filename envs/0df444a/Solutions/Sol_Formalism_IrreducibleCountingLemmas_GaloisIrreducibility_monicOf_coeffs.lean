-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:29.139607+00:00
-- url     : https://prove2.me/submissions/9bfbc7fa-fac9-4bd8-890b-764dfe08438b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {p : K[X]} (hp : p.Monic) (hN : p.natDegree = N) :
    monicOf (fun i : Fin N => p.coeff i) = p := by
  subst hN
  rw [monicOf, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  exact hp.as_sum.symm
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

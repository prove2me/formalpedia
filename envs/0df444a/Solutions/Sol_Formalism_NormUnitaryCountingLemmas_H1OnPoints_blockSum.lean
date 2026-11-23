-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.blockSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.053284+00:00
-- url     : https://prove2.me/submissions/1aa2fba0-571f-43e5-bd6f-78d1d96f6d51

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {N n : ℕ} {ν : Fin N → ℕ} (d : Fin N × Fin n →₀ ℕ)
    (hd : Finsupp.weight (blockWt N n) d = ν) (j : Fin N) : ∑ k, d (j, k) = ν j := by
  have h := congrFun hd j
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Finset.sum_apply, Pi.smul_apply, blockWt, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fintype.sum_prod_type] at h
  simpa [Finset.sum_ite_eq, Finset.sum_comm] using h
end Formalism.NormUnitaryCountingLemmas.H1OnPoints

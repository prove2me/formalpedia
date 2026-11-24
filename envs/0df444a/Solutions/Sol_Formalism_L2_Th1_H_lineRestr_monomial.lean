-- Prove2me | solution 1 for Formalism.L2.Th1.H.lineRestr_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:01.629461+00:00
-- url     : https://prove2.me/submissions/65ce9414-6904-42ce-831c-43b0be8304c9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {K : Type*} [CommRing K] {n : Type*} [Fintype n] (v : n → K) (d : n →₀ ℕ) :
    (d.prod fun s e => (PowerSeries.C (v s) * PowerSeries.X : PowerSeries K) ^ e)
      = PowerSeries.C (∏ i, v i ^ d i) * PowerSeries.X ^ (∑ i, d i) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
end Formalism.L2.Th1.H

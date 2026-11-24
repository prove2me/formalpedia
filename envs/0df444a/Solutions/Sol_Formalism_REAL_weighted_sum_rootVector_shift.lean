-- Prove2me | solution 1 for Formalism.REAL.weighted_sum_rootVector_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:57.191862+00:00
-- url     : https://prove2.me/submissions/b5018138-55cb-4c65-a834-ce7c7d9f6e5a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ν : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, -((i : ℕ) : ℝ) * (ν + root a b) i) =
      (∑ i : Fin n, -((i : ℕ) : ℝ) * ν i) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  simp only [root, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring
end Formalism.REAL

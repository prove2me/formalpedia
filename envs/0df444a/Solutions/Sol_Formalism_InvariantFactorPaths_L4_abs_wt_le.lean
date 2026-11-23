-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.abs_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:03.739687+00:00
-- url     : https://prove2.me/submissions/c4d8920d-5088-40a5-aa2b-eaac4d04a608

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    |wt LL j c m| ≤ ((∑ v, m v : ℕ) : ℤ) := by
  unfold wt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun i : Fin N => ((m (i, c) : ℕ) : ℤ)) fun i _ => ?_).trans ?_
  · split_ifs <;> simp
  · calc ∑ i : Fin N, ((m (i, c) : ℕ) : ℤ) ≤ ∑ i : Fin N, ∑ c' : Fin r, ((m (i, c') : ℕ) : ℤ) :=
          Finset.sum_le_sum fun i _ =>
            Finset.single_le_sum (f := fun c' => ((m (i, c') : ℕ) : ℤ)) (fun _ _ => by positivity)
              (Finset.mem_univ c)
      _ = ((∑ v, m v : ℕ) : ℤ) := by simp [Fintype.sum_prod_type]
end Formalism.InvariantFactorPaths.L4

-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_norm_product_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:28.065721+00:00
-- url     : https://prove2.me/submissions/22040491-594a-4369-a67b-7fc3314ccdc0

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealNormProductLowerBound := by
  intro E _ _ _ aa haa x hx hx0
  have h1 := absNorm_le_abs_norm_of_mem' E aa haa x hx hx0
  have h2 : (∏ w : InfinitePlace E, w x) ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    rw [← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [IsTotallyComplex.mult_eq]
  have h3 : (0 : ℝ) ≤ ∏ w : InfinitePlace E, w x := Finset.prod_nonneg fun w _ => apply_nonneg w x
  rw [← Real.sqrt_sq h3, h2]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h1)
end Formalism.HermitianLatticeCounting.P

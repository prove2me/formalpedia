-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lOneNorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:37.710138+00:00
-- url     : https://prove2.me/submissions/2d587f03-b949-4c54-b16f-1ac430bfee74

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {P : Type} (a b : P →₀ ℂ) : lOneNorm (a + b) ≤ lOneNorm a + lOneNorm b := by
  classical
  have hs : (a + b).support ⊆ a.support ∪ b.support := Finsupp.support_add
  rw [lOneNorm_eq_sum _ _ hs, lOneNorm_eq_sum a _ Finset.subset_union_left, lOneNorm_eq_sum b _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using norm_add_le (a i) (b i)
end Formalism.HermitianLatticeCounting.P

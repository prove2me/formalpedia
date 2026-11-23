-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mul_cutoff_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:20.865438+00:00
-- url     : https://prove2.me/submissions/df7348fc-526d-41c5-9a66-76700a180baf

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

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
theorem _root_.solution {K L y : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (h : L < y) :
    y * TruncationCutoff K L y = L ^ K * y ^ (1 - K) := by
  have hy : 0 < y := hL.trans h
  have h1 : (L / y) ^ K ≤ 1 :=
    Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).2 h.le) hK
  rw [TruncationCutoff, if_neg hy.ne', min_eq_right h1, Real.div_rpow hL.le hy.le, sub_eq_add_neg,
    Real.rpow_add hy, Real.rpow_one, Real.rpow_neg hy.le, div_eq_mul_inv]
  ring
end Formalism.HermitianLatticeCounting.P

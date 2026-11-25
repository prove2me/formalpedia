-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normInvEntryLeMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:53.076929+00:00
-- url     : https://prove2.me/submissions/14335bee-2abc-471b-a9d5-bcf75e46a5aa

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : InverseEntryMinor := by
  intro n M P hP hdet i j
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Ring.inverse_eq_inv,
    norm_inv, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (hP j i) (norm_nonneg _)
end Formalism.HermitianLatticeCounting.P

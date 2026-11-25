-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:15.105231+00:00
-- url     : https://prove2.me/submissions/5666b6f0-42ee-4b0d-8d97-697b7599103f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_det
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_len

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.GramDetEqProdDistances := by
  intro V _ _ l y
  rw [gc_det]
  push_cast
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [gc_len]
end Formalism.HermitianLatticeCounting.P

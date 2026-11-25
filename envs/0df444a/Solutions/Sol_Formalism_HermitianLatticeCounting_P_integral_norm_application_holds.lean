-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_norm_application_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:49.417313+00:00
-- url     : https://prove2.me/submissions/9c32509f-b0f8-497f-8e8d-36e67eae19ac

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_prod_max_inv_le_prod_max__76aced230095

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.NormGeOneMaxBound := by
  intro ι _ G D A hG h1 hD
  constructor
  · rw [Finset.prod_pow, Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => by positivity) (prod_max_inv_le_prod_max' ι G hG h1) A
  · apply Finset.prod_le_prod
    · intro v _; positivity
    · intro v _
      apply pow_le_pow_left₀ (by positivity)
      apply max_le
      · have := sq_nonneg ‖D v‖; linarith
      · have := hD v; linarith
end Formalism.HermitianLatticeCounting.P

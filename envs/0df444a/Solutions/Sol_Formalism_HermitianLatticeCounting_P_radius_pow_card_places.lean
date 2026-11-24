-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.radius_pow_card_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:42.717889+00:00
-- url     : https://prove2.me/submissions/eff7ce30-718c-4bf6-a80b-9f70b98c2876

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_idealRadius_pos
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_radius_sq_pow_card_places

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
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    idealRadius E aa ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) := by
  have h := radius_sq_pow_card_places E aa haa
  have h0 : 0 ≤ idealRadius E aa ^ Fintype.card (InfinitePlace E) := (pow_pos (idealRadius_pos E aa haa) _).le
  rw [← h, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq h0]
end Formalism.HermitianLatticeCounting.P

-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.radius_sq_pow_card_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:28.672737+00:00
-- url     : https://prove2.me/submissions/1e1fdba1-559f-4ace-85a4-76ac90d52448

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_absNorm_pos_of_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_infinite_places_pos

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
    (idealRadius E aa ^ 2) ^ Fintype.card (InfinitePlace E) = (FractionalIdeal.absNorm aa : ℝ) := by
  have hp := absNorm_pos_of_ne_zero E aa haa
  have hc := card_infinite_places_pos E
  rw [← pow_mul, idealRadius, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  have : 1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)) * ((2 * Fintype.card (InfinitePlace E) : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rw [this, Real.rpow_one]
end Formalism.HermitianLatticeCounting.P

-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.absNorm_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:38.550297+00:00
-- url     : https://prove2.me/submissions/aa2bad8b-aaf9-42ef-90f9-76d73cd4e4e1

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
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    (0 : ℝ) < (FractionalIdeal.absNorm aa : ℝ) := by
  have h0 : FractionalIdeal.absNorm aa ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact haa
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa) (Ne.symm h0)
end Formalism.HermitianLatticeCounting.P

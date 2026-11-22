-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ycond_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:45.080992+00:00
-- url     : https://prove2.me/submissions/47fb6836-c88d-40ff-93a6-79f383364f3e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) : YCond p (r := r) LL j (⊤ : WithTop ℤ) = ⊤ := by
  refine le_antisymm le_top (le_sSup ⟨?_, fun c d x _ => Submodule.mem_top⟩)
  intro x _
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m _
  exact (le_top : ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
end Formalism.CountingSumsFrames

-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.binK_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.76781+00:00
-- url     : https://prove2.me/submissions/2416abef-6bb7-4fce-aae1-6187827c578f

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial
namespace Formalism.GM.ProgressionMeanBounds
theorem _root_.solution (K : Type) [Field K] (k : ℕ) : (binK K k).natDegree ≤ k := by
  unfold binK
  exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree K k).le
end Formalism.GM.ProgressionMeanBounds

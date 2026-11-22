-- Prove2me | solution 1 for Formalism.GM.FockB.letterAt_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:20.150884+00:00
-- url     : https://prove2.me/submissions/eeec378c-523e-418b-a44b-b4c9572e6fe6

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} (D : BlockData N)
variable (p : ℕ) [Fact p.Prime]
variable {D}
namespace Formalism.GM.FockB
theorem _root_.solution {k : ℕ} (h : k ≤ N - 1) : (D.letterAt k : ℕ) = k := by
  simp [BlockData.letterAt, h]
end Formalism.GM.FockB

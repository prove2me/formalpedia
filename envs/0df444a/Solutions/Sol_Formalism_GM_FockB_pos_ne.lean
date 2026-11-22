-- Prove2me | solution 1 for Formalism.GM.FockB.pos_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:27.364796+00:00
-- url     : https://prove2.me/submissions/684ea5e8-8c32-4094-81ba-c6adc026536a

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
theorem _root_.solution (hB : D.BlockOK) {i i' : Fin D.T.t} (h : i ≠ i') : D.T.pos i ≠ D.T.pos i' :=
  fun h' => h (hB.1.1.injective h')
end Formalism.GM.FockB

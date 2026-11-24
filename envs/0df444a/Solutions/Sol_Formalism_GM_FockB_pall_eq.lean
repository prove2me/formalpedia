-- Prove2me | solution 1 for Formalism.GM.FockB.pall_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:45.472654+00:00
-- url     : https://prove2.me/submissions/425b95af-8bc5-463b-822f-dad551e2617e

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
namespace Formalism.GM.FockB
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (Y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp Y = chainP (wA D) (eA D) (zA D) (sA D) (zzA D) (oA D j jp) (nA D j jp) (LA D) Y := by
  simp only [chainP, LA, List.foldr_cons, List.foldr_map]
  rfl
end Formalism.GM.FockB

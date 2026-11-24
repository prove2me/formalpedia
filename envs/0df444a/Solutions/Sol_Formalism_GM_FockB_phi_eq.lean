-- Prove2me | solution 1 for Formalism.GM.FockB.phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:06.267386+00:00
-- url     : https://prove2.me/submissions/5d7ac833-daa9-43d1-8d08-445238e5535e

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) :
    D.phiAll p (r := r) j jp = chainPhi (wA D) (eA D) (zzA D) (oA D j jp) (nA D j jp) (LA D) := by
  simp only [chainPhi, LA, List.foldr_cons, List.foldr_map]
  rfl
end Formalism.GM.FockB

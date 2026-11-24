-- Prove2me | solution 1 for Formalism.GM.FockB.ehat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:45.145829+00:00
-- url     : https://prove2.me/submissions/507bd7b1-117f-4b58-b590-29ef80797780

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
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp =
      chainE (wA D) (eA D) (zA D) (sA D) (jA D j jp) (LA D) := by
  simp only [chainE, LA, List.map_cons, List.prod_cons, List.map_map]
  rw [mul_comm, Fin.prod_univ_def]
  rfl
end Formalism.GM.FockB

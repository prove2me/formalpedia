-- Prove2me | solution 1 for Formalism.GM.FockB.deg_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:44.170818+00:00
-- url     : https://prove2.me/submissions/2c7d7508-a2a6-414c-a467-1fab8ebdcea6

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_pos_ne
import Theorems.Thm_Formalism_GM_FockB_pos_ne_succ
import Theorems.Thm_Formalism_GM_FockB_letterAt_val

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
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  have h1 := hB.2.1 i
  have h2 := hB.2.2.2
  have hv : (D.letterAt (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := letterAt_val (by omega)
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (by
      rw [hv]; have := pos_ne hB (Ne.symm hi'); have := pos_ne_succ hB i' i; omega)) (by simp),
    if_pos (Or.inr hv), if_neg (by intro h; rw [h] at hv; omega)]
  simp
end Formalism.GM.FockB

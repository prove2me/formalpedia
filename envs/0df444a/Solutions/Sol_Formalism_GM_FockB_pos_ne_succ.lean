-- Prove2me | solution 1 for Formalism.GM.FockB.pos_ne_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:12.635674+00:00
-- url     : https://prove2.me/submissions/d8bc3d49-c8cc-426d-a9a0-711a88d16350

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
theorem _root_.solution (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨h1, hv1, -⟩ := hB.1.2.1 i
  obtain ⟨h2, -, hv2⟩ := hB.1.2.1 i'
  have e : (⟨D.T.pos i, by omega⟩ : Fin N) = ⟨D.T.pos i' + 1, h2⟩ := Fin.ext h
  rw [e] at hv1
  rw [hv1] at hv2
  exact Bool.noConfusion hv2
end Formalism.GM.FockB

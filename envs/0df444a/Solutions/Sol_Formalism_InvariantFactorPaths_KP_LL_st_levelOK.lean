-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_levelOK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.543939+00:00
-- url     : https://prove2.me/submissions/eb05ccad-9744-4ee5-9dc2-fa65554c6392

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) (h : D.LevelOK j jp)
    (hl : l ≤ min (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1)))) :
    D.LevelOK (Function.update j kk l) jp := by
  delta Formalism.GM.M.BlockData.LevelOK at h ⊢
  refine ⟨fun i => ?_, h.2⟩
  rw [Function.update_apply]
  split_ifs with hi
  · subst hi
    exact ⟨le_trans hl (min_le_left _ _), le_trans hl (min_le_right _ _)⟩
  · exact h.1 i
end Formalism.InvariantFactorPaths.KP.LL

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_wv_ne_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.74714+00:00
-- url     : https://prove2.me/submissions/8875e5b6-0513-471f-b248-de081d0c5af7

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
theorem _root_.solution (hB : D.BlockOK) (kk : Fin D.T.t) (c d : Fin r) : wv D kk c ≠ ev D kk d := by
  intro h
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨-, hlt, -, hN⟩ := hB'
  have h2 := hlt kk
  have h3 := D.uPos.2
  have h1 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  change min (D.T.pos kk) N = min (D.T.pos kk + 1) N at h1
  omega
end Formalism.InvariantFactorPaths.KP.LL

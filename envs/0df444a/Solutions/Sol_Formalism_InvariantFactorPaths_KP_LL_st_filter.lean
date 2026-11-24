-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_filter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.906509+00:00
-- url     : https://prove2.me/submissions/228f0dfb-fbe2-47b8-8c6f-36e0ff497025

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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (t k : ℕ) (hk : k < t) :
    (univ.filter (fun i : Fin t => i.val < k + 1)) = insert ⟨k, hk⟩ (univ.filter (fun i : Fin t => i.val < k)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  constructor
  · intro h
    omega
  · intro h
    omega
end Formalism.InvariantFactorPaths.KP.LL

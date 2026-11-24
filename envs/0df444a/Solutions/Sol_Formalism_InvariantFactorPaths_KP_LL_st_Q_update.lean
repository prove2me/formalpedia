-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_Q_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:48.999147+00:00
-- url     : https://prove2.me/submissions/45a2bf5a-ee16-4099-8cd9-7f92ec4d2067

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
theorem _root_.solution (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) :
    stQ p (r := r) D k kk (Function.update j kk l) jp = stQ p D k kk j jp := by
  have h : (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ Function.update j kk l i) =
      ∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]
  simp only [stQ, h]
end Formalism.InvariantFactorPaths.KP.LL

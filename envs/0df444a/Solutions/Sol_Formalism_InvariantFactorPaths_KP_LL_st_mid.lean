-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.3708+00:00
-- url     : https://prove2.me/submissions/b3152d05-2ea9-4926-919f-565b7883ed3c

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_drop
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_Pt

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
theorem _root_.solution (hB : D.BlockOK) (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D k j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
          (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hP : PL p D ((List.finRange D.T.t).drop k) j jp x =
      tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
        (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x) := by
    rw [st_drop _ k hk]
    exact st_Pt p hB j jp ⟨k, hk⟩ _
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x = _
  rw [hE, hP]
  simp only [stQ]
  ring
end Formalism.InvariantFactorPaths.KP.LL

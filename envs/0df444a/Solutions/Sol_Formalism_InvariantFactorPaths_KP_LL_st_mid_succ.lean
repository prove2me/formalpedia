-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_mid_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:41.575237+00:00
-- url     : https://prove2.me/submissions/14231277-d589-424d-9bb6-3f4ec749bfb3

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_filter

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
theorem _root_.solution (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D (k + 1) j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        (X (zi D r ⟨k, hk⟩) ^ D.T.z ⟨k, hk⟩ * PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hZ : (∏ i : Fin D.T.t with i.val < k + 1,
      (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i) =
      (X (zi D r ⟨k, hk⟩) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z ⟨k, hk⟩ *
        ∏ i : Fin D.T.t with i.val < k, (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i := by
    rw [st_filter _ k hk, Finset.prod_insert (by simp)]
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k + 1, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x = _
  rw [hE, hZ]
  simp only [stQ]
  ring
end Formalism.InvariantFactorPaths.KP.LL

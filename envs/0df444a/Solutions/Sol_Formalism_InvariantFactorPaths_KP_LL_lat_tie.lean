-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.lat_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:33.261799+00:00
-- url     : https://prove2.me/submissions/e0943c8f-48b2-49df-8b54-5507eae9b8ed

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_int_Fpow
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_free
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_pow_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_Y_iter
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_yz_int
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_yz_mk
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_yz_y


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
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by
  intro x hx
  have := span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) •
    (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  rw [LinearMap.smul_apply, tieF_pow_gen hB i y g
    (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)),
    ← smul_mul_assoc, ← map_smul]
  refine Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy)))
    (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩
end Formalism.InvariantFactorPaths.KP.LL

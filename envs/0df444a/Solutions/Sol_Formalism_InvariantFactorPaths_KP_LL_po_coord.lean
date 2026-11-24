-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:11:45.422012+00:00
-- url     : https://prove2.me/submissions/9e3dd16f-afbc-4e81-a0bc-8d40a049d0f7

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_pow_right
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_pow_left
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_int
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pderiv_xi_rename_chainEmb_eq_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_xi_div
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_Y_iter
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_chainEmb_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wU_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_free
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
theorem _root_.solution (hU : HypU p (r := r) D) (j : Fin D.T.t → ℕ) (c : Fin r) (k jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k) x) ∈ Lat p D (r := r) j (jp + k) := by
  intro x hx
  have := span_map_mem ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
    ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k)) _ (Lat p D (r := r) j (jp + k)) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  have hg' := po_xi_div c k hg
  have e : ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • ((po_d (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) ^ k))
      (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t) ((k.factorial : ℚ_[p])⁻¹ • (po_d (D.uPos, c) ^ k) y) *
        ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r D.T.t c) ^ k) g) := by
    have h1 := po_pow_left (p := p) (chainEmb N r D.T.t) chainEmb_inj (D.uPos, c) y
      (xi_free hg' (fun d => wU_ne_xi (D := D) c d)) k
    rw [← Module.End.mul_eq_comp, (commute_pderiv _ _).mul_pow, LinearMap.smul_apply, Module.End.mul_apply,
      po_pow_right _ (pderiv_xi_rename_chainEmb_eq_zero (D := D) y c), map_smul, smul_mul_assoc, ← h1, mul_smul_comm, map_smul,
      smul_smul, sq, mul_inv]
    rfl
  rw [e, Nat.sub_sub] at *
  exact Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (po_Y_iter hU c j k jp y (yz_y hy)))
    (po_int _ k (yz_int hy)), _, hg', rfl⟩
end Formalism.InvariantFactorPaths.KP.LL

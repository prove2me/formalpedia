-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_xi_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:28.753369+00:00
-- url     : https://prove2.me/submissions/8f128de4-3ca0-4319-9a56-8410ffa4dc2e

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_int
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_R_pow

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
omit [NeZero r]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {t b : ℕ} (c : Fin r) (k : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]}
    (hg : g ∈ XiPolZ p N r t b) :
    ((k.factorial : ℚ_[p])⁻¹ • (po_d (xiVar N r t c) ^ k) g) ∈ XiPolZ p N r t (b - k) := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  exact Submodule.mem_inf.mpr ⟨(po_R p N r t (b - k)).smul_mem _ (po_R_pow c k b h1), po_int _ k h2⟩
end Formalism.InvariantFactorPaths.KP.LL

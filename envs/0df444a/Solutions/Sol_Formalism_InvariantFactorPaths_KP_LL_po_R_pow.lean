-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_R_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:29.886794+00:00
-- url     : https://prove2.me/submissions/a283757c-0529-4b5c-b273-68d9a100db57

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_R_step

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
theorem _root_.solution {t : ℕ} (c : Fin r) (k : ℕ) : ∀ (b : ℕ) {g : MvPolynomial (BVar N r t) ℚ_[p]},
    g ∈ po_R p N r t b → (po_d (xiVar N r t c) ^ k) g ∈ po_R p N r t (b - k) := by
  induction k with
  | zero => intro b g hg; simpa using hg
  | succ k ih =>
    intro b g hg
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact po_R_step c (ih b hg)
end Formalism.InvariantFactorPaths.KP.LL

-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.frz_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:59.018882+00:00
-- url     : https://prove2.me/submissions/b9c464f6-4c98-4117-b761-c029d9ce9aa0

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_frz_monomial
import Theorems.Thm_Formalism_GM_leadingTermLemmas_E_pow_X_mul
import Theorems.Thm_Formalism_GM_leadingTermLemmas_leading_vector_add_linked

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) :
    frz K LL ρ n (monomial m 1) =
      (tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n)) := by
  rw [frz_monomial LL ρ hv, leading_vector_add_linked LL ρ e m hme, gv, ← E_pow_X_mul, ← Module.End.mul_apply, ← pow_add,
    Nat.add_sub_cancel' hme]
end Formalism.GM.leadingTermLemmas

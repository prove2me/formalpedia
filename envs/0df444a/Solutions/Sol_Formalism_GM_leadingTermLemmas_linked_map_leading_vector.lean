-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.linked_map_leading_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:57.953293+00:00
-- url     : https://prove2.me/submissions/5a6eef73-8fb9-486e-ac1d-aad92d95ece9

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_pderiv_W_sq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_F_eta_pow

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
theorem _root_.solution (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) :
    tieF (wW (N := N)) eη (V0 (K := K) LL ρ e m n) = X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gF LL ρ e m := by
  unfold V0 gF
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h, if_pos h, F_eta_pow ρ _ _ (pderiv_W_sq LL ρ hv m)]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]
end Formalism.GM.leadingTermLemmas

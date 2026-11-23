-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.leading_vector_add_linked
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:09.274361+00:00
-- url     : https://prove2.me/submissions/d8c77941-a390-46b0-95ff-ec4a22273aec

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_E_pow_X_mul

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
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) :
    V0 (K := K) LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n) =
      X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m := by
  unfold V0 Yh gv
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h, if_pos h, h, Nat.sub_self, pow_zero, Module.End.one_apply, map_zero, add_zero]
  · rw [if_neg h, if_neg h, zero_add, ← Module.End.mul_apply, ← pow_succ',
      show m (Fin.last N, ρ) - e - 1 + 1 = m (Fin.last N, ρ) - e by omega, E_pow_X_mul]
end Formalism.GM.leadingTermLemmas

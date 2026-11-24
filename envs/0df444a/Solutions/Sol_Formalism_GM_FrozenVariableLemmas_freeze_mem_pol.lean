-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freeze_mem_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:02.782458+00:00
-- url     : https://prove2.me/submissions/0c3ed782-05bc-43bc-9f75-3092a1ff9f93

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_weight_fst
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freeze_isWH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (hn : LL.total ≤ n) {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.Pol p r LL) :
    M.freeze p LL ρ n f ∈ M.Pol p r (LL.snoc n) := by
  suffices hs : (↑(M.freeze p LL ρ n f).support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆
      {m | M.MultiDeg (LL.snoc n) m} from hs
  intro m hm i
  have key := freeze_isWH p LL ρ n (fun j => if j = i then 1 else 0) hf (mem_support_iff.mp hm)
  have hw : Finsupp.weight (fun y : Fin (N + 1) × Fin r => if y.1 = i then 1 else 0) m = ∑ c, m (i, c) := by
    rw [weight_fst (fun j => if j = i then 1 else 0) m]
    simp
  rw [← hw, key]
  have ht : LL.total = ∑ b, LL.deg b := rfl
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.castSucc_ne_last, if_false, if_true, zero_add, one_mul, smul_eq_mul, mul_one,
      M.Letters.snoc, Fin.lastCases_last]
    rw [← ht]
    omega
  | cast j =>
    simp only [(Fin.castSucc_ne_last _).symm, Fin.castSucc_inj, if_false, add_zero, smul_eq_mul, mul_zero,
      zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, M.Letters.snoc,
      Fin.lastCases_castSucc]
end Formalism.GM.FrozenVariableLemmas

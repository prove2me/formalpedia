-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.sep_self_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:11.228803+00:00
-- url     : https://prove2.me/submissions/2979860c-e981-42cc-87c4-23312f230d70

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InterlacingSeparation
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_card_erase_Iset
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_factor_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {nu : Fin n → ℤ} (h : Interlace lam nu) :
    |sep lam nu nu| ≤ (lam 0 - lam (Fin.last n) + n + 1) ^
      (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) := by
  set W : ℤ := lam 0 - lam (Fin.last n) + n + 1 with hW
  have inner : ∀ i : Fin n, |∏ y ∈ (Iset lam (B0 lam nu) i).erase (nu i), ev nu (y - (i : ℤ))|
      ≤ W ^ (n * (min (len lam i) (B0 lam nu)).toNat) := by
    intro i
    rw [Finset.abs_prod, ← card_erase_Iset h i, pow_mul, ← Finset.prod_const (W ^ n)]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
    intro y hy
    have hyI := (Finset.mem_erase.mp hy).2
    unfold ev
    rw [Finset.abs_prod]
    calc ∏ j, |nu j - (j : ℤ) - (y - (i : ℤ))| ≤ ∏ _j : Fin n, W :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => factor_bound h i j y hyI)
      _ = W ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold sep
  rw [Finset.abs_prod, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => inner i)
end Formalism.LogVandermondeBounds.flipTwoThree

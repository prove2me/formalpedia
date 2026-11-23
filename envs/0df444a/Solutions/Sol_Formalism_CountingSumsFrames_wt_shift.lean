-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wt_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:16.043687+00:00
-- url     : https://prove2.me/submissions/f164217f-895c-4371-9b31-8617bfe02771

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_shift_apply
import Theorems.Thm_Formalism_CountingSumsFrames_wt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d c' : Fin r) (i : Fin N) (hi : (i : ℕ) < j)
    (m : Fin N × Fin r →₀ ℕ) :
    (LL.vec i = true → 1 ≤ m (i, d) → wt LL j c' (Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) ∧
    (LL.vec i = false → 1 ≤ m (i, c) → wt LL j c' (Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) := by
  have e1 : ∀ e : Fin r, (∑ x : Fin N, (if (x : ℕ) < j then (if LL.vec x then (1 : ℤ) else -1) else 0) *
      (if (i, e) = (x, c') then (1 : ℤ) else 0)) = (if LL.vec i then (1 : ℤ) else -1) * (if e = c' then 1 else 0) := by
    intro e
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  constructor
  · intro hv hm1
    have hs := fun w => shift_apply m (i, c) (i, d) w hm1
    rw [wt_eq, wt_eq]
    simp only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]
    try simp
    try (split_ifs <;> ring)
  · intro hv hm1
    have hs := fun w => shift_apply m (i, d) (i, c) w hm1
    rw [wt_eq, wt_eq]
    simp only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]
    try simp
    try (split_ifs <;> ring)
end Formalism.CountingSumsFrames

-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.supd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:41.403812+00:00
-- url     : https://prove2.me/submissions/279f4b62-dd01-4e6a-90c2-fa49b5c56b40

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (u u' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) (hu' : IsUniU u') :
    supd (u * u') = supd u + supd u' := by
  unfold supd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ ((Fin.castSucc_lt_succ : i.castSucc < i.succ)).ne]
  · rw [hu.1, hu'.1]
    ring
  · rintro c ⟨hc1, hc2⟩
    rcases lt_or_gt_of_ne hc1 with h1 | h1
    · rw [hu.2 _ _ h1, zero_mul]
    · have h2 : (c : ℕ) ≠ (i : ℕ) + 1 := fun h3 => hc2 (Fin.ext (by simp [h3]))
      have h4 : i.succ < c := by
        rw [Fin.lt_iff_val_lt_val] at h1 ⊢
        simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
        omega
      rw [hu'.2 _ _ h4, mul_zero]
end Formalism.EigenvalueLevelCeiling

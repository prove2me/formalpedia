-- Prove2me | solution 1 for Formalism.REAL.sum_update_second_index_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:27.155735+00:00
-- url     : https://prove2.me/submissions/5a0108aa-6526-403a-ac4f-0d25ab2bdfb3

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {M : Type*} [AddCommMonoid M] {j : ℕ} (i : Fin j) (c d : Fin n)
    (f : (Fin j → Fin n × Fin n) → (Fin j → Fin n × Fin n) → M) :
    ∑ α, (if (α i).2 = d then f α (Function.update α i ((α i).1, c)) else 0) =
      ∑ β, (if (β i).2 = c then f (Function.update β i ((β i).1, d)) β else 0) := by
  refine Finset.sum_nbij' (fun α => Function.update α i ((α i).1, (Equiv.swap c d) (α i).2))
    (fun β => Function.update β i ((β i).1, (Equiv.swap c d) (β i).2))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro α _; simp
  · intro β _; simp
  · intro α _
    by_cases hc : (α i).2 = d
    · have hα : Function.update α i ((α i).1, d) = α := by
        rw [← hc]; exact Function.update_eq_self i α
      simp [hc, hα]
    · have hne : (Equiv.swap c d) (α i).2 ≠ c := by
        intro h; apply hc
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        exact h
      simp [hc, hne]
end Formalism.REAL

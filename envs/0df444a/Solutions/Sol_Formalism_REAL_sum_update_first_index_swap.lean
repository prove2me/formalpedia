-- Prove2me | solution 1 for Formalism.REAL.sum_update_first_index_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:26.410382+00:00
-- url     : https://prove2.me/submissions/a8d090aa-6e8d-405b-905f-09cb6940360a

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
    ∑ α, (if (α i).1 = c then f α (Function.update α i (d, (α i).2)) else 0) =
      ∑ β, (if (β i).1 = d then f (Function.update β i (c, (β i).2)) β else 0) := by
  refine Finset.sum_nbij' (fun α => Function.update α i ((Equiv.swap c d) (α i).1, (α i).2))
    (fun β => Function.update β i ((Equiv.swap c d) (β i).1, (β i).2))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro α _; simp
  · intro β _; simp
  · intro α _
    by_cases hc : (α i).1 = c
    · have hα : Function.update α i (c, (α i).2) = α := by
        rw [← hc]; exact Function.update_eq_self i α
      simp [hc, hα]
    · have hne : (Equiv.swap c d) (α i).1 ≠ d := by
        intro h; apply hc
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact h
      simp [hc, hne]
end Formalism.REAL

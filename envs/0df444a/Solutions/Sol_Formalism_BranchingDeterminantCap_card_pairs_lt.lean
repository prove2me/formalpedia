-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.card_pairs_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.071995+00:00
-- url     : https://prove2.me/submissions/f22968cb-6fb3-421e-b427-88e476e54a0b

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2)).card =
      (n + 1) * n / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  dsimp only
  have h : ∀ a : Fin (n + 1), (∑ b : Fin (n + 1), if a < b then 1 else 0) = n - (a : ℕ) := by
    intro a
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    omega
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - k) (n + 1)]
  have hr := Finset.sum_range_reflect (fun k => k) (n + 1)
  simp only [Nat.add_sub_cancel] at hr
  rw [hr, Finset.sum_range_id, Nat.add_sub_cancel]
end Formalism.BranchingDeterminantCap

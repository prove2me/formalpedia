-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.range_le_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:13.050936+00:00
-- url     : https://prove2.me/submissions/5ee5f9da-f104-4309-852e-695a60042160

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_iota_neg
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_iota_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) :
    (psi h).range ≤
      Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} := by
  rintro x ⟨⟨e, k⟩, rfl⟩
  rw [psi_apply]
  have hA : ((iota (m + 2) e, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure
      {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} := by
    rcases Int.units_eq_one_or e with rfl | rfl
    · rw [iota_one]
      exact Subgroup.one_mem _
    · rw [iota_neg]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : ((wgen s m, 1, 1) : GalL (m + 2)) ∈ Subgroup.closure
      {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.2 rfl))
  have heq : ((iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val, 1, 1) : GalL (m + 2))
      = (iota (m + 2) e, 1, 1) * (wgen s m, 1, 1) ^ (Multiplicative.toAdd k).val := by
    rw [Prod.pow_mk, Prod.pow_mk, one_pow, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one]
  rw [heq]
  exact Subgroup.mul_mem _ hA (Subgroup.pow_mem _ hB _)
end Formalism.TwoAdicCyclotomicDecomposition

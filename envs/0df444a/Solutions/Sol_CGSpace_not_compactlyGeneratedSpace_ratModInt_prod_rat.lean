-- Prove2me | solution 1 for CGSpace.not_compactlyGeneratedSpace_ratModInt_prod_rat
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:18:17.347077+00:00
-- url     : https://prove2.me/submissions/ea805ef5-3803-470e-8392-f39688a2b03e

import Mathlib
import Theorems.Thm_CGSpace_isQuotientMap_prodMap
import Theorems.Thm_CGSpace_not_isQuotientMap_prodMap_id_rat

open Topology TopologicalSpace

set_option autoImplicit false

open CGSpace

namespace Sol_CGSpace_not_compactlyGeneratedSpace_ratModInt_prod_rat

/-- The product topology of `(ℚ/ℤ) × ℚ` is not compactly generated: otherwise the product
topologies of `ℚ × ℚ` and of `(ℚ/ℤ) × ℚ` would both coincide with their `k`-ifications, and the
product of the quotient map `ℚ → ℚ/ℤ` with `id` would be a quotient map for the product
topologies. -/
theorem not_cg :
    ¬ CompactlyGeneratedSpace (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) := by
  intro hcg
  -- `ℚ/ℤ` is a quotient of the sequential space `ℚ`, hence sequential, hence compactly generated.
  have hq : IsQuotientMap (Quot.mk (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n)) :=
    isQuotientMap_quot_mk
  have : SequentialSpace (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n)) := hq.sequentialSpace
  -- The product of the two quotient maps is a quotient map for the `k`-ified product topologies.
  have key := CGSpace.isQuotientMap_prodMap.{0} hq (IsQuotientMap.id (X := ℚ))
  -- Both product topologies are compactly generated, so they equal their `k`-ifications.
  have h₁ : (instTopologicalSpaceProd : TopologicalSpace (ℚ × ℚ)) =
      TopologicalSpace.compactlyGenerated.{0} (ℚ × ℚ) := eq_compactlyGenerated
  have h₂ : (instTopologicalSpaceProd :
      TopologicalSpace (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ)) =
      TopologicalSpace.compactlyGenerated.{0}
        (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) := eq_compactlyGenerated
  rw [← h₁, ← h₂] at key
  exact CGSpace.not_isQuotientMap_prodMap_id_rat key

end Sol_CGSpace_not_compactlyGeneratedSpace_ratModInt_prod_rat

theorem solution :
    ¬ CompactlyGeneratedSpace (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) ∧
      ¬ SequentialSpace (Quot (fun x y : ℚ => ∃ m n : ℤ, x = m ∧ y = n) × ℚ) := by
  refine ⟨Sol_CGSpace_not_compactlyGeneratedSpace_ratModInt_prod_rat.not_cg, fun hseq => ?_⟩
  -- A sequential space is compactly generated.
  have := hseq
  exact Sol_CGSpace_not_compactlyGeneratedSpace_ratModInt_prod_rat.not_cg inferInstance

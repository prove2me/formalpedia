-- Prove2me | solution 1 for DeletionCode.RelationSupport.isolated_coordinate_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:53.116788+00:00
-- url     : https://prove2.me/submissions/452ee9dc-7945-40fa-867b-864181fe1c17

import Definitions.Def_DeletionCode_WitnessAlgebra
import Definitions.Def_DeletionCode_RelationSupport

set_option autoImplicit true
open DeletionCode DeletionCode.RelationSupport
open SignedSupport
open scoped BigOperators
namespace DeletionCode.RelationSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (i : I) (g : Gram L)
    (ha : a i ≠ 0) (hgi : G i g ≠ 0)
    (hother : ∀ j, j ≠ i → G j g = 0) : w g ≠ 0 := by
  classical
  have heq : (w g : ℚ) = a i * (G i g : ℚ) := by
    rw [hrel g]
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hother j hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  intro hz
  have hcast : (G i g : ℚ) ≠ 0 := by exact_mod_cast hgi
  have hne := mul_ne_zero ha hcast
  apply hne
  simpa only [hz, Int.cast_zero] using heq.symm
end DeletionCode.RelationSupport

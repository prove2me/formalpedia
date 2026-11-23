-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integer_group_preservation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:07.685143+00:00
-- url     : https://prove2.me/submissions/ac64ba97-ae82-4ee8-a52d-3f847537a896

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := by
  intro E _ _ g a b c d h
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have mem : ∀ x y : E, IsInt x → IsInt y → (∃ w : 𝓞 E, x + y = (g : E) * (w : E)) →
      (x, y) ∈ (ZZ g : Set (E × E)) := by
    intro x y hx hy hw
    simp only [ZZ, Set.mem_setOf_eq]
    exact ⟨hx, hy, hw⟩
  have out : ∀ x y : E, (x, y) ∈ (ZZ g : Set (E × E)) → IsInt x ∧ IsInt y := by
    intro x y hxy
    simp only [ZZ, Set.mem_setOf_eq] at hxy
    exact ⟨hxy.1, hxy.2.1⟩
  have hg : IsInt (g : E) := by simpa using hI (g : 𝓞 E)
  have h0 : IsInt (0 : E) := by simpa using hI 0
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have p1 := out _ _ (h _ (mem _ _ hg h0 ⟨1, by simp⟩))
  have p2 := out _ _ (h _ (mem _ _ h0 hg ⟨1, by simp⟩))
  have p3 := out _ _ (h _ (mem _ _ h1 hm1 ⟨0, by simp⟩))
  simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg, ← sub_eq_add_neg] at p1 p2 p3
  refine ⟨?_, ?_, ?_, ?_, p3.1, p3.2⟩
  · rw [mul_comm]; exact p1.1
  · rw [mul_comm]; exact p2.1
  · rw [mul_comm]; exact p1.2
  · rw [mul_comm]; exact p2.2
end Formalism.HermitianLatticeCounting.P

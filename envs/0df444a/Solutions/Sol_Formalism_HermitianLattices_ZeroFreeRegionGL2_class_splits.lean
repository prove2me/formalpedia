-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.class_splits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:20.918478+00:00
-- url     : https://prove2.me/submissions/75c717c2-d868-4488-a090-d1bf6efc7463

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ClassSplit := by
  intro y q₁ d hq hd hM
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have main : ∀ p : ℕ, p.Prime → p ∣ (d + 1) / 4 → SplitsIn d p := by
    intro p hp hdiv
    have := Fact.mk hp
    refine ⟨0, 1, zero_ne_one, ?_, ?_⟩ <;> simp [(ZMod.natCast_eq_zero_iff _ _).2 hdiv]
  have odd : ∀ p : ℕ, p.Prime → p ∣ d + 1 → p ∣ (d + 1) / 4 := by
    intro p hp hdiv
    by_cases h2 : p = 2
    · subst h2; omega
    · rw [← h4] at hdiv
      rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
      · exfalso
        have : p ∣ 2 ^ 2 := by simpa using h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
      · exact h
  refine ⟨main _ hq (odd _ hq ((Dvd.intro _ rfl).trans hM)), fun p hp hpy => ?_⟩
  by_cases h2 : p = 2
  · subst h2; exact main 2 hp (by omega)
  · apply main _ hp (odd _ hp _)
    refine Dvd.dvd.trans ?_ hM
    apply Dvd.dvd.mul_left
    apply Finset.dvd_prod_of_mem (fun p => p)
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, Nat.le_floor hpy⟩, hp⟩
    have := hp.two_le; omega
end Formalism.HermitianLattices.ZeroFreeRegionGL2

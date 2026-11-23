-- Prove2me | solution 1 for Formalism.HC.Der.Rd.cycRat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:39.086826+00:00
-- url     : https://prove2.me/submissions/985a8199-4039-477b-8ab9-f4ceace20435

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
namespace Formalism.HC.Der.Rd
theorem _root_.solution (m : ℕ) : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨fun h h0 => absurd (Set.mem_singleton_iff.1 h) h0, fun x => ?_⟩
    have htop : Algebra.adjoin ℚ ((Polynomial.cyclotomic 0 ℚ).rootSet
        (Polynomial.cyclotomic 0 ℚ).SplittingField) = ⊤ :=
      Polynomial.SplittingField.adjoin_rootSet _
    rw [Polynomial.cyclotomic_zero, Polynomial.rootSet_one, Algebra.adjoin_empty] at htop
    have hx : x ∈ (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) := by
      rw [show (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) = ⊤ from htop]
      exact Algebra.mem_top
    exact (bot_le : (⊥ : Subalgebra ℚ (CyclotomicField 0 ℚ)) ≤ _) hx
  · haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero (m : ℚ) := ⟨by exact_mod_cast hm.ne'⟩
    exact CyclotomicField.isCyclotomicExtension m ℚ
end Formalism.HC.Der.Rd

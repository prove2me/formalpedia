-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenA.primes_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:12.573332+00:00
-- url     : https://prove2.me/submissions/e31c47bd-7f86-4961-b6bd-3e3e22001a0e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenA_mem_of_disjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
namespace Formalism.MainNotions.BridgeLevelGenA
theorem _root_.solution (g : R) (hg : g ≠ 0) :
    {P : Ideal R | P.IsPrime ∧ Disjoint (coprS g : Set R) (P : Set R)}.Finite := by
  have hI : Ideal.span {g} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg
  refine ((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥ |>.subset ?_
  rintro P ⟨hP, hd⟩
  by_cases hP0 : P = ⊥
  · exact Or.inl hP0
  · refine Or.inr ⟨⟨P, hP, hP0⟩, ?_, rfl⟩
    show P ∣ Ideal.span {g}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact mem_of_disjoint g hP hP0 hd
end Formalism.MainNotions.BridgeLevelGenA

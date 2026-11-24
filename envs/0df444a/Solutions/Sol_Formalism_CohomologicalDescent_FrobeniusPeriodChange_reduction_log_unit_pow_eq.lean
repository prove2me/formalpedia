-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_log_unit_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:30.488999+00:00
-- url     : https://prove2.me/submissions/24fb25de-febd-4e6d-820a-a19e754ede4e

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l] (red : O →+* F)
    (u : ℤ_[l]ˣ) (c r : ℤ_[l]) (m : ℤ) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hr : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * r) :
    red (algebraMap ℤ_[l] O r) = -red (algebraMap ℤ_[l] O c) * ((m : ℤ) : F) := by
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have key : ∀ k : ℕ, ∃ s : ℤ_[l],
      (u : ℤ_[l]) ^ k = 1 + (l : ℤ_[l]) * ((k : ℤ_[l]) * c) + (l : ℤ_[l]) ^ 2 * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨(k : ℤ_[l]) * c ^ 2 + s + s * (l : ℤ_[l]) * c, ?_⟩
      rw [pow_succ, hs, hu]
      push_cast
      ring
  have ht : ∃ t : ℤ_[l], r = -((m : ℤ) : ℤ_[l]) * c + (l : ℤ_[l]) * t := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(k : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) * (u : ℤ_[l]) ^ k = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        simp
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r + (k : ℤ_[l]) * c +
          (l : ℤ_[l]) * (r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s)) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨-(r * (k : ℤ_[l]) * c + s + r * (l : ℤ_[l]) * s), ?_⟩
      push_cast
      linear_combination h3
    · obtain ⟨s, hs⟩ := key k
      have h1 : ((u ^ (-(-(k : ℤ))) : ℤ_[l]ˣ) : ℤ_[l]) = (u : ℤ_[l]) ^ k := by
        rw [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]
      rw [hr, hs] at h1
      have h2 : (l : ℤ_[l]) * (r - (k : ℤ_[l]) * c - (l : ℤ_[l]) * s) = 0 := by
        linear_combination h1
      have h3 := (mul_eq_zero.1 h2).resolve_left hl0
      refine ⟨s, ?_⟩
      push_cast
      linear_combination h3
  obtain ⟨t, ht⟩ := ht
  rw [ht]
  simp only [map_add, map_mul, map_neg, map_intCast, map_natCast, CharP.cast_eq_zero, zero_mul,
    add_zero]
  ring
end Formalism.CohomologicalDescent.FrobeniusPeriodChange

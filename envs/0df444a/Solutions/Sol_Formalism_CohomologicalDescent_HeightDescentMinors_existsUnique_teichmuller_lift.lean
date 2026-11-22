-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.existsUnique_teichmuller_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:06.11394+00:00
-- url     : https://prove2.me/submissions/c68d30ca-aa86-401e-9275-951938794991

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mem_mu_iff_pow_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_eq_zero_iff_norm_lt_one

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (x : ZMod l) (hx : x ≠ 0) : ∃! d, d ∈ mu l ∧ PadicInt.toZMod d = x := by
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := l)) x
  set F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1 with hFdef
  have hF : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1 := by
    intro z; simp [hFdef]
  have hF' : ∀ z : ℤ_[l], Polynomial.aeval z (Polynomial.derivative F) =
      ((l - 1 : ℕ) : ℤ_[l]) * z ^ (l - 1 - 1) := by
    intro z; simp [hFdef, Polynomial.derivative_X_pow]
  have h1 : ‖Polynomial.aeval a F‖ < 1 := by
    rw [← toZMod_eq_zero_iff_norm_lt_one, hF, map_sub, map_pow, ha, ZMod.pow_card_sub_one_eq_one hx,
      map_one, sub_self]
  have h2 : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [← PadicInt.isUnit_iff]
    by_contra hnu
    have h3 := PadicInt.not_isUnit_iff.mp hnu
    rw [← toZMod_eq_zero_iff_norm_lt_one, hF', map_mul, map_natCast, map_pow, ha] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · have h4 := Nat.le_of_dvd (prime_sub_one_pos l) ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have h5 := prime_sub_one_pos l
      omega
    · exact hx (eq_zero_of_pow_eq_zero h)
  obtain ⟨z, hz0, hza, -, huniq⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
  rw [h2] at hza huniq
  refine ⟨z, ⟨(mem_mu_iff_pow_eq_one l).mpr (sub_eq_zero.mp ((hF z).symm.trans hz0)), ?_⟩, ?_⟩
  · have h6 := (toZMod_eq_zero_iff_norm_lt_one l (z - a)).mpr hza
    rw [map_sub, ha, sub_eq_zero] at h6
    exact h6
  · rintro d ⟨hd, hdx⟩
    apply huniq
    · rw [hF, (mem_mu_iff_pow_eq_one l).mp hd, sub_self]
    · rw [← toZMod_eq_zero_iff_norm_lt_one, map_sub, hdx, ha, sub_self]
end Formalism.CohomologicalDescent.HeightDescentMinors

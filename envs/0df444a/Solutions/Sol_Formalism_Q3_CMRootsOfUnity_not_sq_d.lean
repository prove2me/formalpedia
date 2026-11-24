-- Prove2me | solution 1 for Formalism.Q3.CMRootsOfUnity.not_sq_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:28.366805+00:00
-- url     : https://prove2.me/submissions/fb6cd07f-922f-4548-880d-9d3cf28104ff

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open Formalism.Q3.CMRootsOfUnity
variable {q : Fin 3 → ℕ}
namespace Formalism.Q3.CMRootsOfUnity
theorem _root_.solution (hq : Hyp3 q) (d : ℤ) (S : Finset (Fin 3)) (hS : S.Nonempty ∨ d < 0)
    (hdq : ∀ i, ¬ (q i : ℤ) ∣ d) :
    ¬ IsSquare ((d : ℚ) * ∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
  classical
  rw [← Int.cast_prod, ← Int.cast_mul, Rat.isSquare_intCast_iff]
  rintro ⟨r, hr⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · rcases hS with ⟨x, hx⟩ | hd
    · simp at hx
    · simp only [Finset.prod_empty, mul_one] at hr
      nlinarith [mul_self_nonneg r]
  · have hp : Prime (q i0 : ℤ) := Nat.prime_iff_prime_int.mp (hq.1 i0).1
    have hprod : d * ∏ i ∈ S, -(q i : ℤ) =
        -(q i0 : ℤ) * (d * ∏ i ∈ S.erase i0, -(q i : ℤ)) := by
      rw [← Finset.mul_prod_erase S (fun i => -(q i : ℤ)) hi0]; ring
    have hpr : (q i0 : ℤ) ∣ r := by
      apply hp.dvd_of_dvd_pow (n := 2)
      rw [sq, ← hr, hprod]
      exact Dvd.dvd.mul_right (dvd_neg.mpr dvd_rfl) _
    obtain ⟨t, rfl⟩ := hpr
    have h0 : (q i0 : ℤ) ≠ 0 := by exact_mod_cast (hq.1 i0).1.ne_zero
    have hrest : (q i0 : ℤ) ∣ d * ∏ i ∈ S.erase i0, -(q i : ℤ) := by
      refine ⟨-(t * t), ?_⟩
      rw [hprod] at hr
      apply mul_left_cancel₀ h0
      linear_combination -hr
    rcases hp.dvd_or_dvd hrest with h | h
    · exact hdq i0 h
    · obtain ⟨i, hi, hdiv⟩ := (hp.dvd_finsetProd_iff _).mp h
      rw [dvd_neg, Int.natCast_dvd_natCast,
        Nat.prime_dvd_prime_iff_eq (hq.1 i0).1 (hq.1 i).1] at hdiv
      exact (Finset.ne_of_mem_erase hi) (hq.2 hdiv).symm
end Formalism.Q3.CMRootsOfUnity

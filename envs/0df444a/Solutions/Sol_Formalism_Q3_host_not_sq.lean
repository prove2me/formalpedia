-- Prove2me | solution 1 for Formalism.Q3.host_not_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:35.369808+00:00
-- url     : https://prove2.me/submissions/3ddc068a-9b4c-411b-853e-1123a170a6bd

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQKummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (q : Fin 3 → ℕ) (hq : Hyp3 q) (S : Finset (Fin 3)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
  obtain ⟨hp, hinj⟩ := hq
  obtain ⟨j, hj⟩ := hS
  intro hsq
  rw [← Int.cast_prod, Rat.isSquare_intCast_iff] at hsq
  obtain ⟨t, ht⟩ := hsq
  have hpj : Prime (q j : ℤ) := Nat.prime_iff_prime_int.mp (hp j).1
  have hdiv : (q j : ℤ) ∣ t * t := by
    rw [← ht]
    exact (dvd_neg.2 (dvd_refl _)).trans (Finset.dvd_prod_of_mem (fun i => -(q i : ℤ)) hj)
  have ht' : (q j : ℤ) ∣ t := (hpj.dvd_or_dvd hdiv).elim id id
  have hsq2 : (q j : ℤ) * q j ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [ht]
    exact mul_dvd_mul ht' ht'
  rw [← Finset.mul_prod_erase S _ hj] at hsq2
  have hrest : (q j : ℤ) ∣ ∏ i ∈ S.erase j, (-(q i : ℤ)) := by
    have e : -(q j : ℤ) * ∏ i ∈ S.erase j, (-(q i : ℤ)) =
        (q j : ℤ) * (-(∏ i ∈ S.erase j, (-(q i : ℤ)))) := by ring
    rw [e] at hsq2
    exact dvd_neg.1 ((mul_dvd_mul_iff_left hpj.ne_zero).1 hsq2)
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hpj _).1 hrest
  have hij : i ≠ j := Finset.ne_of_mem_erase hi
  have hdi' : q j ∣ q i := Int.natCast_dvd_natCast.1 (dvd_neg.1 hdi)
  have heq := (Nat.prime_dvd_prime_iff_eq (hp j).1 (hp i).1).1 hdi'
  exact hij (hinj heq.symm)
end Formalism.Q3

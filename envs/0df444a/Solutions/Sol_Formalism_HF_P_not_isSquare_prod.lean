-- Prove2me | solution 1 for Formalism.HF.P.not_isSquare_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:11.156778+00:00
-- url     : https://prove2.me/submissions/7a700f08-04e3-4e7b-bd33-c08f1aad36ef

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (S : Finset (Fin k)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((fun i => -(q i : ℤ)) i : ℤ) : ℚ)) := by
  classical
  have hcast : (∏ i ∈ S, (((fun i => -(q i : ℤ)) i : ℤ) : ℚ)) =
      ((∏ i ∈ S, (-(q i : ℤ)) : ℤ) : ℚ) := by push_cast; rfl
  rw [hcast, Rat.isSquare_intCast_iff]
  rintro ⟨m, hm⟩
  obtain ⟨j, hj⟩ := hS
  have hp : Prime (q j : ℤ) := Nat.prime_iff_prime_int.mp (hq j)
  have hsplit : (∏ i ∈ S, (-(q i : ℤ))) = (-(q j : ℤ)) * ∏ i ∈ S.erase j, (-(q i : ℤ)) :=
    (Finset.mul_prod_erase S _ hj).symm
  have hdn : (q j : ℤ) ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [hsplit]; exact Dvd.dvd.mul_right (dvd_neg.mpr dvd_rfl) _
  rw [hm] at hdn
  have hdm : (q j : ℤ) ∣ m := by
    rcases hp.dvd_or_dvd hdn with h | h <;> exact h
  have hsq : (q j : ℤ) * q j ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [hm]; exact mul_dvd_mul hdm hdm
  rw [hsplit] at hsq
  obtain ⟨c, hc⟩ := hsq
  have hne : (q j : ℤ) ≠ 0 := by exact_mod_cast (hq j).ne_zero
  have hP : (q j : ℤ) ∣ ∏ i ∈ S.erase j, (-(q i : ℤ)) := by
    refine ⟨-c, ?_⟩
    have : (q j : ℤ) * (∏ i ∈ S.erase j, (-(q i : ℤ))) = (q j : ℤ) * ((q j : ℤ) * -c) := by
      linear_combination (-1 : ℤ) * hc
    exact mul_left_cancel₀ hne this
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finset_prod_iff hp _).mp hP
  have hdi' : q j ∣ q i := by
    have := (dvd_neg.mp hdi)
    exact_mod_cast this
  have heq : q j = q i := (Nat.prime_dvd_prime_iff_eq (hq j) (hq i)).mp hdi'
  exact (Finset.ne_of_mem_erase hi) (hinj heq).symm
end Formalism.HF.P

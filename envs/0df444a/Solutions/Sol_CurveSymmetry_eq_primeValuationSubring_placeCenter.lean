-- Prove2me | solution 1 for CurveSymmetry.eq_primeValuationSubring_placeCenter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:32.173466+00:00
-- url     : https://prove2.me/submissions/7d701638-be4f-487e-b337-e97847258d47

-- Solution generated from lean/DedekindPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
omit [IsDedekindDomain A] in
lemma ofPrime_congr (B : ValuationSubring K) {P Q : Ideal B} [P.IsPrime] [Q.IsPrime]
    (h : P = Q) : B.ofPrime P = B.ofPrime Q := by
  subst h
  rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
/-- The type `A_P` of the valuation subring is a DVR. -/
lemma primeValuationSubring_dvr (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (primeValuationSubring K P hP) := by
  have := primeLocalization_dvr (K := K) P hP
  let e : primeLocalization K P ≃+* primeValuationSubring K P hP :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
/-- A valuation subring other than `K` that contains `A_P` equals `A_P`. -/
theorem eq_primeValuationSubring_of_le (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥)
    (O : ValuationSubring K) (hle : primeValuationSubring K P hP ≤ O) (htop : O ≠ ⊤) :
    O = primeValuationSubring K P hP := by
  let B := primeValuationSubring K P hP
  have := primeValuationSubring_dvr (K := K) P hP
  have hof := ValuationSubring.ofPrime_idealOfLE B O hle
  by_cases hb : B.idealOfLE O hle = ⊥
  · exfalso
    apply htop
    rw [← hof, ofPrime_congr B hb, ValuationSubring.ofPrime_bot]
  · have hmax := (inferInstance : (B.idealOfLE O hle).IsPrime).isMaximal_of_ne_bot hb
    rw [← hof, ofPrime_congr B (eq_maximalIdeal hmax), ValuationSubring.ofPrime_top]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
theorem solution (O : ValuationSubring K)
    (hO : ∀ a : A, algebraMap A K a ∈ O) (htop : O ≠ ⊤) :
    O = primeValuationSubring K (placeCenter K O hO) (placeCenter_ne_bot O hO htop) := by
  apply eq_primeValuationSubring_of_le _ _ O _ htop
  intro x hx
  obtain ⟨a, s, hs, rfl⟩ := hx
  exact mul_mem (hO a) (inv_mem_of_notMem_placeCenter O hO hs)
end

#print axioms solution

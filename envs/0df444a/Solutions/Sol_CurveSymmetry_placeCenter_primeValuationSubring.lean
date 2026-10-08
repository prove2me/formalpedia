-- Prove2me | solution 1 for CurveSymmetry.placeCenter_primeValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:19.300974+00:00
-- url     : https://prove2.me/submissions/ad4d8048-6b60-4af9-83c0-110c685018a9

-- Solution generated from lean/DedekindPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Valuation.ValuationSubring

section
open CurveSymmetry
set_option autoImplicit false
open IsLocalRing
variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]
theorem solution (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    placeCenter K (primeValuationSubring K P hP) (algebraMap_mem_primeValuationSubring hP) = P := by
  ext a
  constructor
  · intro ha
    by_contra haP
    have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP :=
      ⟨1, a, haP, by simp⟩
    rw [mem_placeCenter] at ha
    have h1 := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr hinv
    rw [map_inv₀] at h1
    have hpos : 0 < (primeValuationSubring K P hP).valuation (algebraMap A K a) := by
      rw [Valuation.pos_iff]
      intro h0
      apply haP
      rw [(IsFractionRing.injective A K) (h0.trans (map_zero _).symm)]
      exact P.zero_mem
    exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr ha)
  · intro haP
    rw [mem_placeCenter]
    by_contra hge
    have hle := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr
      (algebraMap_mem_primeValuationSubring hP a)
    have heq := le_antisymm hle (not_lt.mp hge)
    have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, heq, inv_one]
    obtain ⟨b, s, hs, he⟩ := hinv
    have ha0 : algebraMap A K a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at heq
      exact zero_ne_one heq
    have hs0 : algebraMap A K s ≠ 0 := by
      intro h0
      apply hs
      rw [(IsFractionRing.injective A K) (h0.trans (map_zero _).symm)]
      exact P.zero_mem
    have hab : algebraMap A K s = algebraMap A K (a * b) := by
      rw [map_mul]
      field_simp at he
      linear_combination he
    rw [IsFractionRing.injective A K hab] at hs
    exact hs (P.mul_mem_right b haP)
end

#print axioms solution

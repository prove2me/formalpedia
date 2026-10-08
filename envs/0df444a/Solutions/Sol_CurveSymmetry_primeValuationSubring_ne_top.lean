-- Prove2me | solution 1 for CurveSymmetry.primeValuationSubring_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:43.203008+00:00
-- url     : https://prove2.me/submissions/59af5d94-0049-4e24-9d56-6b52bed3f61a

-- Solution generated from lean/DedekindPlaces.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_placeCenter_primeValuationSubring
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
    primeValuationSubring K P hP ≠ ⊤ := by
  intro htop
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hmem : a ∈ placeCenter K (primeValuationSubring K P hP)
      (algebraMap_mem_primeValuationSubring hP) := by
    rw [placeCenter_primeValuationSubring]
    exact haP
  have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP := by
    rw [htop]
    exact ValuationSubring.mem_top _
  rw [mem_placeCenter] at hmem
  have h1 := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr hinv
  rw [map_inv₀] at h1
  have hpos : 0 < (primeValuationSubring K P hP).valuation (algebraMap A K a) := by
    rw [Valuation.pos_iff]
    intro h0
    exact ha0 ((IsFractionRing.injective A K) (h0.trans (map_zero _).symm))
  exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr hmem)
end

#print axioms solution

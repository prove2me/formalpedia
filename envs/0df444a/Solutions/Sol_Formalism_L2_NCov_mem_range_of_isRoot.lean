-- Prove2me | solution 1 for Formalism.L2.NCov.mem_range_of_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T09:42:13.5169+00:00
-- url     : https://prove2.me/submissions/81fdf575-3d6a-4115-98f0-1e4981be3533

import Mathlib

open Polynomial

theorem solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (P : (FractionRing O)[X]) (hm : P.Monic)
    (hc : ∀ i, P.coeff i ∈ (algebraMap O (FractionRing O)).range) {μ : FractionRing O}
    (hμ : P.IsRoot μ) :
    μ ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let f : O →+* FractionRing O := algebraMap O (FractionRing O)
  have hf : Function.Injective f := IsFractionRing.injective O (FractionRing O)
  have hinv0 : Function.invFun f 0 = 0 := by
    simpa using Function.leftInverse_invFun hf 0
  -- Lift P coefficientwise along the injective map f.
  let Q : O[X] := P.sum (fun i a => monomial i (Function.invFun f a))
  have hcoeff (n : ℕ) : Q.coeff n = Function.invFun f (P.coeff n) := by
    simp only [Q, coeff_sum, coeff_monomial]
    rw [sum_def, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have hn0 : P.coeff n = 0 := by simpa [mem_support_iff] using h
      simp [hn0, hinv0]
  have hQmap : Q.map f = P := by
    ext n
    simp only [coeff_map, hcoeff]
    exact Function.invFun_eq (hc n)
  have hQmonic : Q.Monic := by
    have := hm
    rw [← hQmap] at this
    exact (Function.Injective.monic_map_iff hf).mpr this
  have hQroot : aeval μ Q = 0 := by
    have hroot : aeval μ P = 0 := by simpa [IsRoot] using hμ
    rw [← hQmap] at hroot
    simpa [aeval_def, eval₂_map] using hroot
  have hInt : IsIntegral O μ := ⟨Q, hQmonic, hQroot⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hInt
  exact ⟨y, hy⟩

-- Prove2me | solution 1 for ExtCitation.exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/63e4b7ef-fdae-56c1-ae06-d84f3fa17a82

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Theorems.Thm_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : primeLocalGaloisGroup (pPrime p), primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup →
        ∀ x ∈ K, ResidualGaloisRep.localAut p s x = x := by
  classical

  let ρ : primeLocalGaloisGroup (pPrime p) →* (PadicAlgCl p →ₗ[ℚ_[p]] PadicAlgCl p) :=
    { toFun := fun s => (ResidualGaloisRep.localAut p s).toLinearMap
      map_one' := by ext x; rfl
      map_mul' := fun s t => by ext x; rfl }
  let M : Rep ℚ_[p] (primeLocalGaloisGroup (pPrime p)) := Rep.of ρ
  haveI : Fact ((pPrime p : Nat.Primes) : ℕ).Prime := ‹Fact p.Prime›
  have hloc : ∀ m : M, ∃ K' : IntermediateField ℚ_[p] (PadicAlgCl p),
      FiniteDimensional ℚ_[p] K' ∧
        ∀ s : primeLocalGaloisGroup (pPrime p), s ∈ K'.fixingSubgroup → M.ρ s m = m := by
    intro m
    refine ⟨IntermediateField.adjoin ℚ_[p] {(m : PadicAlgCl p)},
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) (m : PadicAlgCl p)).isIntegral, ?_⟩
    intro s hs
    have hs' := (mem_fixingSubgroup_iff (M := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).mp hs
      (m : PadicAlgCl p) (IntermediateField.mem_adjoin_simple_self ℚ_[p] (m : PadicAlgCl p))
    exact hs'
  obtain hglob := (ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
    (pPrime p) M).mpr hloc

  let b := Module.finBasis ℚ_[p] K
  choose F hFfin hF using fun i : Fin (Module.finrank ℚ_[p] K) => hglob ((b i : K) : PadicAlgCl p)
  haveI : ∀ i, FiniteDimensional ℚ (F i) := hFfin
  refine ⟨⨆ i, F i, inferInstance, ?_⟩
  intro s hs x hx
  have hfix : ∀ i, ResidualGaloisRep.localAut p s ((b i : K) : PadicAlgCl p) = ((b i : K) : PadicAlgCl p) := by
    intro i
    have hi : primeLocalToGlobal (pPrime p) s ∈ (F i).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (le_iSup F i) hs
    exact hF i s hi

  have hx' : (⟨x, hx⟩ : K) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr ⟨x, hx⟩).symm
  have hxv : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : K) : PadicAlgCl p) := by
    have h1 := congrArg (fun y : K => (y : PadicAlgCl p)) hx'
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h1
    exact h1
  rw [hxv, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hfix i]

#print axioms solution

end S_ExtCitation_exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le
end P2MW
export P2MW.S_ExtCitation_exists_finiteDimensional_fixingSubgroup_comap_primeLocalToGlobal_le (solution)

-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b0b6569f-00b2-510f-a32e-1f7f69e6a1d3

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    [Fact (A.DecompositionIsometric ℚ)]
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)
    (hι_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        actZ (ι τ) = 1)
    (u : 𝒰.P.TorusPoints)
    (hu : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        gal (ι τ) (𝒰.eFull u) = 𝒰.eFull u)
    (τ : ↥(A.decompositionSubgroup ℚ))
    (hτ : (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion) (hs : ∀ c, s c = τ • c) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by
  refine 𝒰.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq (ι τ) (hι_inertia τ hτ) s
    (fun c => by rw [hι]; exact hs c) (fun c => ?_) u (hu τ hτ)
  rw [hs c]
  exact ValuationSubring.valuation_smul_completion τ c

end S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq (solution)

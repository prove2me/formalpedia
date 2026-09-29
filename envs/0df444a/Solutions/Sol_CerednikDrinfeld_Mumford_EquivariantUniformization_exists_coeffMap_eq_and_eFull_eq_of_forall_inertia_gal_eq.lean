-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8252dad2-4f14-5dbc-ba87-2da6944a23cf

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq

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
    (z : T)
    (hz : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        gal (ι τ) z = z) :
    ∃ u : 𝒰.P.TorusPoints,
      (∀ τ : ↥(A.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) →
          𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
      𝒰.eFull u = z := by
  obtain ⟨u, rfl⟩ := 𝒰.eFull_surjective z
  exact ⟨u, fun τ hτ s hs =>
    𝒰.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq ι hι hι_inertia u hz τ hτ s hs, rfl⟩

end S_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq (solution)

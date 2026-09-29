-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlue.specialLevel_isField_isReduced_dim_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f9cde5bf-913f-5eda-a11a-521f53195259

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_isReduced_quotient_level_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_isMaximal_or_mem_minimalPrimes_quotient_level_zero
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero
import Theorems.Thm_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_locallyOfFiniteType_and_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    :
    IsField (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) ∧ IsReduced (Gl.Z 0) ∧
    (∀ z : Gl.Z 0, IsClosed ({z} : Set (Gl.Z 0)) ∨ closure ({z} : Set (Gl.Z 0)) ∈ irreducibleComponents (Gl.Z 0)) ∧
    (∀ C ∈ irreducibleComponents (Gl.Z 0), Set.Infinite C) := by
  haveI := hdvr
  have hmax : (Ideal.span ({π} : Set 𝒪)).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact IsLocalRing.maximalIdeal.isMaximal 𝒪
  have hfield : IsField (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (by rw [zero_add, pow_one]; exact hmax)
  refine ⟨hfield, ?_⟩

  haveI := (MumfordGlue.locallyOfFiniteType_and_quasiCompact 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N Gl 0).1
  letI : Field (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) := hfield.toField
  haveI : JacobsonSpace ↥(Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}))) :=
    inferInstanceAs (JacobsonSpace (PrimeSpectrum (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})))
  haveI : JacobsonSpace ↥(Gl.Z 0) := LocallyOfFiniteType.jacobsonSpace (Gl.zb 0)
  obtain ⟨S, hS⟩ := Gl.ζ_cover 0
  exact AlgebraicGeometry.isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover (Gl.Z 0)
    (Matrix.GeneralLinearGroup (Fin 2) K₀)
    (fun _ => (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))
    (fun h => Gl.ζ h 0) (fun h => Gl.ζ_isOpenImmersion h 0)
    (fun z => by obtain ⟨h, -, hz⟩ := hS z; exact ⟨h, hz⟩)
    (fun _ => chartERing.isReduced_quotient_level_zero 𝒪 π r hmax)
    (fun _ p hp => chartERing.isMaximal_or_mem_minimalPrimes_quotient_level_zero 𝒪 π r hmax p hp)
    (fun _ p hp => chartERing.infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero 𝒪 π r hmax p hp)

end S_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlue_specialLevel_isField_isReduced_dim_infinite (solution)

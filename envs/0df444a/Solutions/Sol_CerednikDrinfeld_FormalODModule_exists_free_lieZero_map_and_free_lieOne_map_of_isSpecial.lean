-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f838a313-edca-52a5-980c-eca6f40a55c3

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial

set_option autoImplicit false

universe u

open TensorProduct

namespace L1aAux

variable {B : Type u} [CommRing B]

theorem exists_free_away (x : PrimeSpectrum B) (L : Type u) [AddCommGroup L] [Module B L]
    [Module.Finite B L] [Module.Flat B L] [Module.FinitePresentation B L] :
    ∃ r : B, r ∉ x.asIdeal ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[B] L) := by
  have hx : x ∈ Module.freeLocus B L := by rw [Module.freeLocus_eq_univ]; trivial
  have : Module.Free (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl L) := hx
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl L) (Localization.AtPrime x.asIdeal)
  exact ⟨r, hr, Module.Free.of_equiv
    (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) L)).equiv.symm⟩

theorem free_away_mul (r s : B) (L : Type u) [AddCommGroup L] [Module B L]
    [Module.Free (Localization.Away r) (Localization.Away r ⊗[B] L)] :
    Module.Free (Localization.Away (r * s)) (Localization.Away (r * s) ⊗[B] L) := by
  letI alg : Algebra (Localization.Away r) (Localization.Away (r * s)) :=
    (IsLocalization.Away.awayToAwayRight (P := Localization.Away (r * s)) r s).toAlgebra
  haveI : IsScalarTower B (Localization.Away r) (Localization.Away (r * s)) := by
    refine IsScalarTower.of_algebraMap_eq fun b => ?_
    rw [RingHom.algebraMap_toAlgebra]
    unfold IsLocalization.Away.awayToAwayRight
    exact (IsLocalization.Away.lift_eq (x := r) _ b).symm
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away r) (Localization.Away (r * s))
      (Localization.Away (r * s)) L)

theorem free_span_image (f : B) (L : Submodule B (Fin 2 → B))
    [Module.Free (Localization.Away f) (Localization.Away f ⊗[B] ↥L)] :
    Module.Free (Localization.Away f)
      ↥(Submodule.span (Localization.Away f)
        ((fun m : Fin 2 → B => fun i => algebraMap B (Localization.Away f) (m i)) '' (L : Set (Fin 2 → B)))) := by
  let coeL : (Fin 2 → B) →ₗ[B] (Fin 2 → Localization.Away f) :=
    LinearMap.pi fun i => (Algebra.linearMap B (Localization.Away f)) ∘ₗ LinearMap.proj i
  haveI : IsLocalizedModule (.powers f) coeL := IsLocalizedModule.pi _ _
  have e := (IsLocalizedModule.isBaseChange (.powers f) (Localization.Away f)
    (L.toLocalized' (Localization.Away f) (.powers f) coeL)).equiv
  have himg : ((fun m : Fin 2 → B => fun i => algebraMap B (Localization.Away f) (m i)) '' (L : Set (Fin 2 → B))) =
      coeL '' (L : Set (Fin 2 → B)) := by
    congr 1
  rw [himg, ← Submodule.localized'_eq_span (Localization.Away f) (.powers f) coeL L]
  exact Module.Free.of_equiv e

end L1aAux

open L1aAux in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B) (hX : X.IsSpecial j)
    (x : PrimeSpectrum B) :
    ∃ f : B, f ∉ x.asIdeal ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieZero ((algebraMap B (Localization.Away f)).comp j)) ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieOne ((algebraMap B (Localization.Away f)).comp j)) := by
  obtain ⟨hc, hi₀, hi₁⟩ := hX
  haveI := hi₀; haveI := hi₁
  haveI : Module.FinitePresentation B ↥(X.lieZero j) := Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation B ↥(X.lieOne j) := Module.finitePresentation_of_projective _ _
  obtain ⟨r₀, hr₀, hF₀⟩ := exists_free_away x ↥(X.lieZero j)
  obtain ⟨r₁, hr₁, hF₁⟩ := exists_free_away x ↥(X.lieOne j)
  haveI := hF₀; haveI := hF₁
  refine ⟨r₀ * r₁, fun h => (x.isPrime.mem_or_mem h).elim hr₀ hr₁, ?_, ?_⟩
  · haveI := free_away_mul r₀ r₁ ↥(X.lieZero j)
    have hspan := (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p j
      (algebraMap B (Localization.Away (r₀ * r₁))) X).2 hc
    rw [← hspan.1]
    exact free_span_image (r₀ * r₁) (X.lieZero j)
  · haveI := free_away_mul r₁ r₀ ↥(X.lieOne j)
    rw [mul_comm]
    have hspan := (CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image p j
      (algebraMap B (Localization.Away (r₁ * r₀))) X).2 hc
    rw [← hspan.2]
    exact free_span_image (r₁ * r₀) (X.lieOne j)

end S_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial (solution)

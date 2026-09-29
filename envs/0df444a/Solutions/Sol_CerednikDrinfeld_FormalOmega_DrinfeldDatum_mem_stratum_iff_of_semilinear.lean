-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.mem_stratum_iff_of_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c38cffd5-471a-5c96-af05-9a5c32d03de1

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace B28Strata

variable {B B' : Type} [CommRing B] [CommRing B'] (f : B →+* B')

theorem map_mem_smul_top {M M' : Type} [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M']
    (τ : M →ₛₗ[f] M') (I : Ideal B) (J : Ideal B') (hIJ : ∀ a ∈ I, f a ∈ J) {m : M}
    (hm : m ∈ I • (⊤ : Submodule B M)) : τ m ∈ J • (⊤ : Submodule B' M') := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun u v hu hv => ?_)
  · rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (hIJ a ha) Submodule.mem_top
  · rw [map_add]; exact Submodule.add_mem _ hu hv

theorem mk_mem_maximalIdeal_smul_top {M : Type} [AddCommGroup M] [Module B M] (x : PrimeSpectrum B) {m : M}
    (hm : m ∈ x.asIdeal • (⊤ : Submodule B M)) :
    LocalizedModule.mk m (1 : x.asIdeal.primeCompl) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal)) •
        (⊤ : Submodule (Localization.AtPrime x.asIdeal) (LocalizedModule x.asIdeal.primeCompl M)) := by
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_) (fun u v hu hv => ?_)
  · rw [← LocalizedModule.mkLinearMap_apply, LinearMap.map_smul_of_tower, LocalizedModule.mkLinearMap_apply,
      ← IsScalarTower.algebraMap_smul (Localization.AtPrime x.asIdeal) a]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime x.asIdeal) x.asIdeal a).mpr ha
  · rw [← LocalizedModule.mkLinearMap_apply, map_add, LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply]
    exact Submodule.add_mem _ hu hv

theorem range_le_smul_top_iff
    {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
    [Module.Invertible B P] [Module.Invertible B Q]
    {P' Q' : Type} [AddCommGroup P'] [Module B' P'] [AddCommGroup Q'] [Module B' Q']
    [Module.Invertible B' P'] [Module.Invertible B' Q']
    (π : P →ₗ[B] Q) (π' : P' →ₗ[B'] Q') (τP : P →ₛₗ[f] P') (τQ : Q →ₛₗ[f] Q')
    (hτP : Submodule.span B' (Set.range τP) = ⊤) (hτQ : Submodule.span B' (Set.range τQ) = ⊤)
    (hc : ∀ s, τQ (π s) = π' (τP s)) (x' : PrimeSpectrum B') :
    LinearMap.range π' ≤ x'.asIdeal • (⊤ : Submodule B' Q') ↔
      LinearMap.range π ≤ (PrimeSpectrum.comap f x').asIdeal • (⊤ : Submodule B Q) := by
  classical
  set x : PrimeSpectrum B := PrimeSpectrum.comap f x' with hx
  have hxx' : ∀ a ∈ x.asIdeal, f a ∈ x'.asIdeal := fun a ha => by
    simpa [hx, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using ha
  constructor
  ·
    intro h'
    by_contra h
    have hbij := Module.Invertible.bijective_localizedModule_map_of_not_range_le π x h

    have hv : ∀ q : Q, ∃ v : B, v ∉ x.asIdeal ∧ v • q ∈ LinearMap.range π := by
      intro q
      obtain ⟨z, hz⟩ := hbij.2 (LocalizedModule.mk q 1)
      induction z using LocalizedModule.induction_on with
      | h pp s =>
        rw [LocalizedModule.map_mk] at hz
        obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hz

        have hu' : (u : B) • π pp = (u : B) • ((s : B) • q) := by
          simpa only [Submonoid.smul_def, one_smul] using hu
        refine ⟨(u : B) * (s : B), ?_, ?_⟩
        · exact x.asIdeal.primeCompl.mul_mem u.2 s.2
        · refine ⟨(u : B) • pp, ?_⟩
          rw [map_smul, hu', ← mul_smul]

    set R' := Localization.AtPrime x'.asIdeal with hR'
    set N : Submodule R' (LocalizedModule x'.asIdeal.primeCompl Q') := ⊤ with hN
    have hle : N ≤ (IsLocalRing.maximalIdeal R') • N := by
      rw [hN]
      intro z _
      induction z using LocalizedModule.induction_on with
      | h q' s' =>

        have hq' : q' ∈ Submodule.span B' (Set.range τQ) := hτQ ▸ Submodule.mem_top
        have key : ∀ q' ∈ Submodule.span B' (Set.range τQ),
            LocalizedModule.mk q' (1 : x'.asIdeal.primeCompl) ∈ (IsLocalRing.maximalIdeal R') •
              (⊤ : Submodule R' (LocalizedModule x'.asIdeal.primeCompl Q')) := by
          intro q' hq'
          induction hq' using Submodule.span_induction with
          | mem w hw =>
            obtain ⟨q, rfl⟩ := hw
            obtain ⟨v, hvx, hvq⟩ := hv q
            have hfv : f v ∉ x'.asIdeal := fun hh => hvx (by simpa [hx, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hh)

            have h1 : f v • τQ q ∈ x'.asIdeal • (⊤ : Submodule B' Q') := by
              rw [← LinearMap.map_smulₛₗ]
              obtain ⟨pp, hpp⟩ := hvq
              rw [← hpp, hc]
              exact h' ⟨τP pp, rfl⟩
            have h2 := mk_mem_maximalIdeal_smul_top x' h1
            have h3 : LocalizedModule.mk (τQ q) (1 : x'.asIdeal.primeCompl) =
                Localization.mk 1 (⟨f v, hfv⟩ : x'.asIdeal.primeCompl) •
                  LocalizedModule.mk (f v • τQ q) (1 : x'.asIdeal.primeCompl) := by
              rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
              exact (LocalizedModule.mk_cancel (⟨f v, hfv⟩ : x'.asIdeal.primeCompl) (τQ q)).symm
            rw [h3]
            exact Submodule.smul_mem _ _ h2
          | zero => rw [LocalizedModule.zero_mk]; exact Submodule.zero_mem _
          | add u w _ _ hu hw =>
            rw [← LocalizedModule.mkLinearMap_apply, map_add, LocalizedModule.mkLinearMap_apply,
              LocalizedModule.mkLinearMap_apply]
            exact Submodule.add_mem _ hu hw
          | smul a w _ hw =>
            rw [← LocalizedModule.mkLinearMap_apply, LinearMap.map_smul_of_tower, LocalizedModule.mkLinearMap_apply]
            rw [← IsScalarTower.algebraMap_smul R' a]
            exact Submodule.smul_mem _ _ hw
        have e : LocalizedModule.mk q' s' = Localization.mk 1 s' • LocalizedModule.mk q' (1 : x'.asIdeal.primeCompl) := by
          rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
        rw [e]
        exact Submodule.smul_mem _ _ (key q' hq')
    have hjac : IsLocalRing.maximalIdeal R' ≤ (⊥ : Ideal R').jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hbot : N = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ N Module.Finite.fg_top hle hjac

    obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R')
      (M := LocalizedModule x'.asIdeal.primeCompl Q')).mp inferInstance
    have : (e.symm 1 : LocalizedModule x'.asIdeal.primeCompl Q') = 0 := by
      have : (e.symm 1) ∈ N := hN ▸ Submodule.mem_top
      rw [hbot] at this
      exact (Submodule.mem_bot R').mp this
    have : (1 : R') = 0 := by simpa using congrArg e this
    exact one_ne_zero this
  ·
    intro h
    rintro _ ⟨p', rfl⟩
    have hp' : p' ∈ Submodule.span B' (Set.range τP) := hτP ▸ Submodule.mem_top
    induction hp' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨s, rfl⟩ := hw
      rw [← hc]
      exact map_mem_smul_top f τQ x.asIdeal x'.asIdeal hxx' (h ⟨s, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
    | smul a w _ hw => rw [map_smul]; exact Submodule.smul_mem _ _ hw

end B28Strata

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B] {B' : Type} [CommRing B'] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B')
    (τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀) (τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁)
    (hτ₀ : Submodule.span B' (Set.range τ₀) = ⊤) (hτ₁ : Submodule.span B' (Set.range τ₁) = ⊤)
    (hPi₀ : ∀ s, τ₁ (Q.Pi₀ s) = Q'.Pi₀ (τ₀ s)) (hPi₁ : ∀ s, τ₀ (Q.Pi₁ s) = Q'.Pi₁ (τ₁ s))
    (x' : PrimeSpectrum B') :
    (x' ∈ Q'.stratum₀ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₀) ∧
      (x' ∈ Q'.stratum₁ ↔ DrinfeldDatum.pointUnder f x' ∈ Q.stratum₁) := by
  haveI := Q.invertible₀; haveI := Q.invertible₁; haveI := Q'.invertible₀; haveI := Q'.invertible₁
  exact ⟨B28Strata.range_le_smul_top_iff (f : B →+* B') Q.Pi₀ Q'.Pi₀ τ₀ τ₁ hτ₀ hτ₁ hPi₀ x',
    B28Strata.range_le_smul_top_iff (f : B →+* B') Q.Pi₁ Q'.Pi₁ τ₁ τ₀ hτ₁ hτ₀ hPi₁ x'⟩

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_mem_stratum_iff_of_semilinear (solution)

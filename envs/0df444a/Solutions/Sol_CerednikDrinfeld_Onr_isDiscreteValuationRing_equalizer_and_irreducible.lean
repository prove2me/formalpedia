-- Prove2me | solution 1 for CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4d109ba6-e48a-5ff5-8548-4ceb8218dfde

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible

set_option autoImplicit false

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (F : Onr ≃ₐ[𝒪] Onr) :
    IsDiscreteValuationRing ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ∧ Irreducible (algebraMap 𝒪 ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) := by
  classical

  set ϖ : Onr := algebraMap 𝒪 Onr π with hϖ
  set I : Ideal Onr := Ideal.span {ϖ} with hI
  set S : Subalgebra 𝒪 Onr := AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr) with hS
  have hmemS : ∀ {x : Onr}, x ∈ S ↔ F x = x := fun {x} => by
    rw [hS]; exact AlgHom.mem_equalizer _ _ _
  have hϖI : ϖ ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self ϖ

  have hunit : ∀ x : Onr, x ∉ I → IsUnit x := by
    intro x hx
    obtain ⟨y, i, hi, hyx⟩ := hOnr_max.exists_inv hx
    have hi' : i ∈ (⊥ : Ideal Onr).jacobson := IsAdicComplete.le_jacobson_bot I hi
    have hu : IsUnit (i * (-1) + 1) := Ideal.mem_jacobson_bot.mp hi' (-1)
    have : y * x = i * (-1) + 1 := by linear_combination hyx
    rw [← this] at hu
    exact isUnit_of_mul_isUnit_right hu

  have hsep : ∀ x : Onr, (∀ k : ℕ, x ∈ I ^ k) → x = 0 := by
    intro x hx
    haveI : IsHausdorff I Onr := hOnr_complete.toIsHausdorff
    exact IsHausdorff.haus' (I := I) x (fun k => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact hx k)
  have hfact : ∀ x : Onr, x ≠ 0 → ∃ (k : ℕ) (u : Onr), IsUnit u ∧ x = ϖ ^ k * u := by
    intro x hx
    have hex : ∃ k : ℕ, x ∉ I ^ k := by
      by_contra h
      push_neg at h
      exact hx (hsep x h)
    have hk₀ : x ∉ I ^ Nat.find hex := Nat.find_spec hex
    have hk₀pos : Nat.find hex ≠ 0 := by
      intro h0
      apply hk₀
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hxk : x ∈ I ^ k := by
      have := Nat.find_min hex (show k < Nat.find hex by omega)
      simpa using this
    rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxk
    obtain ⟨u, hu⟩ := hxk
    refine ⟨k, u, hunit u ?_, hu⟩
    intro huI
    apply hk₀
    rw [hI] at huI
    rw [hk, hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu, pow_succ]
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.mp huI)

  have hFϖ : F ϖ = ϖ := by rw [hϖ]; exact F.commutes π
  have hϖS : ϖ ∈ S := hmemS.mpr hFϖ
  have hsat : ∀ (k : ℕ) (y : Onr), ϖ ^ k * y ∈ S → y ∈ S := by
    intro k y h
    rw [hmemS] at h ⊢
    rw [map_mul, map_pow, hFϖ] at h
    exact mul_left_cancel₀ (pow_ne_zero k hπ0) h
  have hinvS : ∀ (u : Onr) (hu : IsUnit u), u ∈ S → ((hu.unit⁻¹ : Onrˣ) : Onr) ∈ S := by
    intro u hu huS
    rw [hmemS] at huS
    rw [hmemS]
    have hvu : ((hu.unit⁻¹ : Onrˣ) : Onr) * u = 1 := hu.val_inv_mul
    have huv : u * ((hu.unit⁻¹ : Onrˣ) : Onr) = 1 := hu.mul_val_inv
    calc F ((hu.unit⁻¹ : Onrˣ) : Onr)
        = F ((hu.unit⁻¹ : Onrˣ) : Onr) * (u * ((hu.unit⁻¹ : Onrˣ) : Onr)) := by rw [huv, mul_one]
      _ = F ((hu.unit⁻¹ : Onrˣ) : Onr) * F u * ((hu.unit⁻¹ : Onrˣ) : Onr) := by rw [huS, mul_assoc]
      _ = F (((hu.unit⁻¹ : Onrˣ) : Onr) * u) * ((hu.unit⁻¹ : Onrˣ) : Onr) := by rw [map_mul]
      _ = ((hu.unit⁻¹ : Onrˣ) : Onr) := by rw [hvu, map_one, one_mul]
  have hunitS : ∀ (s : ↥S), IsUnit (s : Onr) → IsUnit s := by
    intro s hu
    exact ⟨⟨s, ⟨((hu.unit⁻¹ : Onrˣ) : Onr), hinvS s hu s.2⟩, Subtype.ext hu.mul_val_inv, Subtype.ext hu.val_inv_mul⟩, rfl⟩

  let ϖS : ↥S := ⟨ϖ, hϖS⟩
  have hϖS_eq : algebraMap 𝒪 ↥S π = ϖS := Subtype.ext (by rw [Subalgebra.coe_algebraMap])
  have hϖ_not_unit : ¬ IsUnit ϖ := fun h => hOnr_max.ne_top (Ideal.eq_top_of_isUnit_mem _ hϖI h)
  have hirr : Irreducible ϖS := by
    refine ⟨fun h => hϖ_not_unit (h.map S.val), fun a b hab => ?_⟩
    have hab' : ϖ = (a : Onr) * (b : Onr) := congrArg Subtype.val hab
    have hmem : (a : Onr) * (b : Onr) ∈ I := hab' ▸ hϖI
    rcases hOnr_max.isPrime.mem_or_mem hmem with ha | hb
    · right
      rw [hI, Ideal.mem_span_singleton] at ha
      obtain ⟨a', ha'⟩ := ha
      apply hunitS
      refine isUnit_iff_exists_inv'.mpr ⟨a', ?_⟩
      apply mul_left_cancel₀ hπ0
      rw [← mul_assoc, ← ha', ← hab', mul_one]
    · left
      rw [hI, Ideal.mem_span_singleton] at hb
      obtain ⟨b', hb'⟩ := hb
      apply hunitS
      refine isUnit_iff_exists_inv.mpr ⟨b', ?_⟩
      apply mul_left_cancel₀ hπ0
      rw [mul_left_comm, ← hb', ← hab', mul_one]

  refine ⟨IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖS, hirr, ?_⟩, hϖS_eq ▸ hirr⟩
  intro x hx
  have hx' : (x : Onr) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨k, u, hu, hxu⟩ := hfact x hx'
  have huS : u ∈ S := hsat k u (hxu ▸ x.2)
  have hunit' : IsUnit (⟨u, huS⟩ : ↥S) := hunitS ⟨u, huS⟩ hu
  refine ⟨k, hunit'.unit, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IsUnit.unit_spec]
  exact hxu.symm

end S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible
end P2MW
export P2MW.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible (solution)

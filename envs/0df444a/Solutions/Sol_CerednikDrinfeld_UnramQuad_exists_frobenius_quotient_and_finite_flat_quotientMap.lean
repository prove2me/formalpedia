-- Prove2me | solution 1 for CerednikDrinfeld.UnramQuad.exists_frobenius_quotient_and_finite_flat_quotientMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/5de39b70-af98-521a-a09e-1ab4f59d0dd9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap

set_option autoImplicit false

namespace F6preAux

section O2

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

abbrev O2 : Subalgebra 𝒪 Onr :=
  AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)

theorem mem_O2_iff (y : Onr) : y ∈ O2 Fr ↔ Fr (Fr y) = y := by
  simp [AlgHom.mem_equalizer]

theorem fr_mem_O2 {y : Onr} (hy : y ∈ O2 Fr) : Fr y ∈ O2 Fr := by
  rw [mem_O2_iff] at hy ⊢
  rw [hy]

theorem fr_symm_eq_fr_of_mem {y : Onr} (hy : y ∈ O2 Fr) : Fr.symm y = Fr y := by
  rw [mem_O2_iff] at hy
  conv_lhs => rw [← hy]
  rw [AlgEquiv.symm_apply_apply]

noncomputable def Fr₂ : ↥(O2 Fr) ≃ₐ[𝒪] ↥(O2 Fr) :=
  AlgEquiv.ofAlgHom
    ((Fr : Onr →ₐ[𝒪] Onr).restrictDomain (O2 Fr) |>.codRestrict (O2 Fr) (fun y => fr_mem_O2 Fr y.2))
    ((Fr : Onr →ₐ[𝒪] Onr).restrictDomain (O2 Fr) |>.codRestrict (O2 Fr) (fun y => fr_mem_O2 Fr y.2))
    (by
      ext y
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_codRestrict, AlgHom.coe_id, id_eq]
      exact (mem_O2_iff Fr (y : Onr)).1 y.2)
    (by
      ext y
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_codRestrict, AlgHom.coe_id, id_eq]
      exact (mem_O2_iff Fr (y : Onr)).1 y.2)

@[scoped simp] theorem coe_Fr₂ (y : ↥(O2 Fr)) : ((Fr₂ Fr y : ↥(O2 Fr)) : Onr) = Fr (y : Onr) := rfl

theorem Fr₂_Fr₂ (y : ↥(O2 Fr)) : Fr₂ Fr (Fr₂ Fr y) = y := by
  ext
  simp only [coe_Fr₂]
  exact (mem_O2_iff Fr (y : Onr)).1 y.2

theorem Fr₂_mul_Fr₂ : Fr₂ Fr * Fr₂ Fr = 1 := by
  ext y
  exact congrArg Subtype.val (Fr₂_Fr₂ Fr y)

theorem Fr₂_sq : Fr₂ Fr ^ 2 = 1 := by
  rw [pow_two, Fr₂_mul_Fr₂]

theorem Fr₂_symm : (Fr₂ Fr).symm = Fr₂ Fr := by
  apply AlgEquiv.ext
  intro y
  rw [AlgEquiv.symm_apply_eq, Fr₂_Fr₂]

theorem Fr₂_algebraMap (x : 𝒪) : Fr₂ Fr (algebraMap 𝒪 (↥(O2 Fr)) x) = algebraMap 𝒪 (↥(O2 Fr)) x :=
  AlgEquiv.commutes _ x

variable (π : 𝒪)

abbrev lvl (n : ℕ) : Ideal ↥(O2 Fr) := Ideal.span {(algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1)}

theorem lvl_map_Fr₂ (n : ℕ) : lvl Fr π n = (lvl Fr π n).map (Fr₂ Fr : ↥(O2 Fr) →+* ↥(O2 Fr)) := by
  rw [Ideal.map_span, Set.image_singleton]
  have h : (Fr₂ Fr : ↥(O2 Fr) →+* ↥(O2 Fr)) ((algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1)) = (algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1) := by
    rw [map_pow]
    exact congrArg (· ^ (n + 1)) (Fr₂_algebraMap Fr π)
  rw [h]

noncomputable def Fr₂lvl (n : ℕ) : (↥(O2 Fr) ⧸ lvl Fr π n) ≃ₐ[𝒪] (↥(O2 Fr) ⧸ lvl Fr π n) :=
  Ideal.quotientEquivAlg (lvl Fr π n) (lvl Fr π n) (Fr₂ Fr) (lvl_map_Fr₂ Fr π n)

theorem Fr₂lvl_mk (n : ℕ) (y : ↥(O2 Fr)) :
    Fr₂lvl Fr π n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (Fr₂ Fr y) := by
  simp [Fr₂lvl]

theorem Fr₂lvl_link (n : ℕ) (y y' : ↥(O2 Fr)) (h : (y' : Onr) = Fr (y : Onr)) :
    Fr₂lvl Fr π n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y' := by
  rw [Fr₂lvl_mk]
  congr 1
  ext
  rw [coe_Fr₂, h]

theorem Fr₂lvl_Fr₂lvl (n : ℕ) (z : ↥(O2 Fr) ⧸ lvl Fr π n) : Fr₂lvl Fr π n (Fr₂lvl Fr π n z) = z := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Fr₂lvl_mk, Fr₂lvl_mk, Fr₂_Fr₂]

theorem Fr₂lvl_sq (n : ℕ) : Fr₂lvl Fr π n ^ 2 = 1 := by
  rw [pow_two]
  ext z
  exact Fr₂lvl_Fr₂lvl Fr π n z

theorem Fr₂lvl_zpow_of_even (n : ℕ) {k : ℤ} (hk : Even k) : Fr₂lvl Fr π n ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, zpow_mul, zpow_ofNat, Fr₂lvl_sq, one_zpow]

theorem Fr₂lvl_zpow_of_odd (n : ℕ) {k : ℤ} (hk : Odd k) : Fr₂lvl Fr π n ^ k = Fr₂lvl Fr π n := by
  obtain ⟨j, rfl⟩ := hk
  rw [zpow_add, zpow_one, zpow_mul, zpow_ofNat, Fr₂lvl_sq, one_zpow, one_mul]

theorem Fr₂lvl_zpow_neg (n : ℕ) (k : ℤ) : Fr₂lvl Fr π n ^ (-k) = Fr₂lvl Fr π n ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [Fr₂lvl_zpow_of_even Fr π n hk, Fr₂lvl_zpow_of_even Fr π n (even_neg.mpr hk)]
  · rw [Fr₂lvl_zpow_of_odd Fr π n hk, Fr₂lvl_zpow_of_odd Fr π n (odd_neg.mpr hk)]

theorem factor_comp_Fr₂lvl (n : ℕ) :
    (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (↥(O2 Fr)) π) (Nat.le_succ (n + 1))))).comp
      (Fr₂lvl Fr π (n + 1)).toRingEquiv.toRingHom =
    (Fr₂lvl Fr π n).toRingEquiv.toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (↥(O2 Fr)) π) (Nat.le_succ (n + 1))))) := by
  apply Ideal.Quotient.ringHom_ext
  ext y
  simp only [RingHom.coe_comp, Function.comp_apply]
  change Ideal.Quotient.factor _ (Fr₂lvl Fr π (n + 1) (Ideal.Quotient.mk _ y)) =
    Fr₂lvl Fr π n (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ y))
  rw [Fr₂lvl_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Fr₂lvl_mk]

theorem mem_O2_of_smul_mem [IsDomain Onr] {c : 𝒪} (hc : algebraMap 𝒪 Onr c ≠ 0) {w : Onr}
    (h : algebraMap 𝒪 Onr c * w ∈ O2 Fr) : w ∈ O2 Fr := by
  rw [mem_O2_iff] at h ⊢
  rw [map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at h
  exact mul_left_cancel₀ hc h

end O2

section Finiteness

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (π : 𝒪)

omit [IsDomain Onr] in
open Polynomial in

theorem pow_sq_sub_self_mem_of_mem_O2 (r : ℕ)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {y : Onr} (hy : y ∈ O2 Fr) : y ^ (r ^ 2) - y ∈ Ideal.span {algebraMap 𝒪 Onr π} := by
  set I := Ideal.span {algebraMap 𝒪 Onr π}
  have h1 : Fr (Fr y) - (Fr y) ^ r ∈ I := hFr (Fr y)
  have h2 : (Fr y) ^ r - (y ^ r) ^ r ∈ I := by
    have := hFr y

    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (Fr y) (y ^ r) r
    rw [hc]; exact I.mul_mem_right _ this
  have h3 : Fr (Fr y) = y := (mem_O2_iff Fr y).1 hy
  have : y - y ^ (r ^ 2) ∈ I := by
    have h12 := I.add_mem h1 h2
    rw [h3, ← pow_mul, ← sq] at h12
    simpa using h12
  simpa using I.neg_mem this

theorem mem_lvl_of_coe_mem (hπ : algebraMap 𝒪 Onr π ≠ 0) (k : ℕ) {y : ↥(O2 Fr)}
    (h : (y : Onr) ∈ Ideal.span {(algebraMap 𝒪 Onr π) ^ k}) :
    y ∈ Ideal.span {(algebraMap 𝒪 (↥(O2 Fr)) π) ^ k} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨w, hw⟩ := h
  have hwmem : w ∈ O2 Fr := by
    refine mem_O2_of_smul_mem Fr (c := π ^ k) ?_ ?_
    · rw [map_pow]; exact pow_ne_zero _ hπ
    · rw [map_pow, ← hw]; exact y.2
  refine ⟨⟨w, hwmem⟩, ?_⟩
  ext
  simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
  exact hw

open Polynomial in

theorem finite_O2_mod (r : ℕ) (hr : 2 ≤ r) (hπ : algebraMap 𝒪 Onr π ≠ 0)
    (hprime : (Ideal.span {algebraMap 𝒪 Onr π}).IsPrime)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π}) :
    Finite (↥(O2 Fr) ⧸ lvl Fr π 0) := by
  set I := Ideal.span {algebraMap 𝒪 Onr π}
  haveI : I.IsPrime := hprime
  haveI : IsDomain (Onr ⧸ I) := Ideal.Quotient.isDomain I
  classical

  set f : (Onr ⧸ I)[X] := X ^ (r ^ 2) - X with hf
  have hf0 : f ≠ 0 := by
    have hlt : 1 < r ^ 2 := by nlinarith
    intro h0
    have := congrArg (fun q : (Onr ⧸ I)[X] => q.coeff (r ^ 2)) h0
    simp only [hf, coeff_sub, coeff_X_pow, if_true, coeff_X, coeff_zero] at this
    rw [if_neg (by omega)] at this
    simp at this

  let φ : ↥(O2 Fr) →+* Onr ⧸ I := (Ideal.Quotient.mk I).comp (O2 Fr).val.toRingHom
  have hφ : ∀ y : ↥(O2 Fr), φ y = Ideal.Quotient.mk I (y : Onr) := fun y => rfl
  have hker : ∀ y : ↥(O2 Fr), φ y = 0 → y ∈ lvl Fr π 0 := by
    intro y hy0
    have hyI : (y : Onr) ∈ I := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem] at hy0; exact hy0
    exact mem_lvl_of_coe_mem Fr π hπ (0 + 1) (y := y) (by simpa using hyI)
  let φbar : ↥(O2 Fr) ⧸ lvl Fr π 0 →+* Onr ⧸ I :=
    Ideal.Quotient.lift (lvl Fr π 0) φ (by
      intro y hy
      rw [Ideal.mem_span_singleton] at hy
      obtain ⟨w, rfl⟩ := hy
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      simp only [zero_add, pow_one, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
      exact I.mul_mem_right _ (Ideal.subset_span rfl))
  have hinj : Function.Injective φbar := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker y hz)
  have hroot : ∀ z : ↥(O2 Fr) ⧸ lvl Fr π 0, φbar z ∈ f.roots.toFinset := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk, Multiset.mem_toFinset, mem_roots hf0, IsRoot.def, hf, eval_sub, eval_pow, eval_X,
      hφ, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact pow_sq_sub_self_mem_of_mem_O2 Fr π r hFr y.2
  let ι : ↥(O2 Fr) ⧸ lvl Fr π 0 → ↥f.roots.toFinset := fun z => ⟨φbar z, hroot z⟩
  have hι : Function.Injective ι := fun a b hab => hinj (Subtype.ext_iff.mp hab)
  exact Finite.of_injective ι hι

theorem finite_O2_lvl (r : ℕ) (hr : 2 ≤ r) (hπ : algebraMap 𝒪 Onr π ≠ 0)
    (hprime : (Ideal.span {algebraMap 𝒪 Onr π}).IsPrime)
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π}) (n : ℕ) :
    Finite (↥(O2 Fr) ⧸ lvl Fr π n) := by
  induction n with
  | zero => exact finite_O2_mod Fr π r hr hπ hprime hFr
  | succ n ih =>
    haveI := ih
    haveI h0 := finite_O2_mod Fr π r hr hπ hprime hFr

    let t : (↥(O2 Fr) ⧸ lvl Fr π (n + 1)) →+ (↥(O2 Fr) ⧸ lvl Fr π n) :=
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 (↥(O2 Fr)) π) (Nat.le_succ (n + 1))))).toAddMonoidHom
    rw [AddMonoidHom.finite_iff_finite_ker_range t]
    refine ⟨?_, inferInstance⟩

    let m : (↥(O2 Fr) ⧸ lvl Fr π 0) →+ (↥(O2 Fr) ⧸ lvl Fr π (n + 1)) :=
      QuotientAddGroup.lift ((lvl Fr π 0).toAddSubgroup)
        (((Ideal.Quotient.mk (lvl Fr π (n + 1))).toAddMonoidHom).comp
          (AddMonoidHom.mulLeft ((algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1))))
        (by
          intro y hy
          change y ∈ lvl Fr π 0 at hy
          rw [Ideal.mem_span_singleton] at hy
          obtain ⟨w, rfl⟩ := hy
          change Ideal.Quotient.mk (lvl Fr π (n + 1)) ((algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1) * _) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          exact ⟨w, by ring⟩)
    have hsurj : ∀ z ∈ t.ker, ∃ u, m u = z := by
      intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hz' : Ideal.Quotient.mk (lvl Fr π n) y = 0 := by
        rw [AddMonoidHom.mem_ker] at hz
        rw [← hz]
        rfl
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz'
      obtain ⟨w, rfl⟩ := hz'
      exact ⟨QuotientAddGroup.mk w, rfl⟩
    let s : (↥(O2 Fr) ⧸ lvl Fr π 0) → t.ker := fun u => ⟨m u, by
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
      change t (Ideal.Quotient.mk (lvl Fr π (n + 1)) ((algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1) * y)) = 0
      simp only [t, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y, rfl⟩⟩
    have hs : Function.Surjective s := by
      rintro ⟨z, hz⟩
      obtain ⟨u, hu⟩ := hsurj z hz
      exact ⟨u, Subtype.ext hu⟩
    exact Finite.of_surjective s hs

theorem flat_O2 [IsDomain 𝒪] [IsDedekindDomain 𝒪] (hinj : Function.Injective (algebraMap 𝒪 Onr)) :
    Module.Flat 𝒪 ↥(O2 Fr) := by
  haveI : Module.IsTorsionFree 𝒪 Onr := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.IsTorsionFree 𝒪 ↥(O2 Fr) := Subalgebra.instIsTorsionFree (O2 Fr)
  infer_instance

end Finiteness

section LevelBase

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (π : 𝒪)

theorem base_le_comap (n : ℕ) :
    Ideal.span {π ^ (n + 1)} ≤ (lvl Fr π n).comap (algebraMap 𝒪 ↥(O2 Fr)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  exact Ideal.subset_span rfl

theorem lvl_eq_map (n : ℕ) : lvl Fr π n = (Ideal.span {π ^ (n + 1)}).map (algebraMap 𝒪 ↥(O2 Fr)) := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

abbrev baseMap (n : ℕ) : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* (↥(O2 Fr) ⧸ lvl Fr π n) :=
  Ideal.quotientMap (lvl Fr π n) (algebraMap 𝒪 ↥(O2 Fr)) (base_le_comap Fr π n)

theorem baseMap_flat (n : ℕ) [Module.Flat 𝒪 ↥(O2 Fr)] : (baseMap Fr π n).Flat := by
  set J : Ideal 𝒪 := Ideal.span {π ^ (n + 1)}

  have hflat : Module.Flat (𝒪 ⧸ J) (↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr))) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (↥(O2 Fr)) J).toLinearEquiv
  have h1 : (Ideal.quotientMap (J.map (algebraMap 𝒪 ↥(O2 Fr))) (algebraMap 𝒪 ↥(O2 Fr)) Ideal.le_comap_map).Flat := by
    have := (RingHom.flat_algebraMap_iff (R := 𝒪 ⧸ J) (S := ↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr)))).mpr hflat
    exact this

  let e : (↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr))) ≃ₐ[𝒪] (↥(O2 Fr) ⧸ lvl Fr π n) :=
    Ideal.quotientEquivAlgOfEq 𝒪 (lvl_eq_map Fr π n).symm
  have hcomp : baseMap Fr π n =
      e.toRingEquiv.toRingHom.comp (Ideal.quotientMap (J.map (algebraMap 𝒪 ↥(O2 Fr))) (algebraMap 𝒪 ↥(O2 Fr)) Ideal.le_comap_map) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk]
    change _ = e (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(O2 Fr) x))
    rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [hcomp]
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mpr h1

theorem baseMap_finite (n : ℕ) [Finite (↥(O2 Fr) ⧸ lvl Fr π n)] : (baseMap Fr π n).Finite := by
  letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n) := (baseMap Fr π n).toAlgebra
  exact Module.Finite.of_finite

end LevelBase

end F6preAux
p2m_reactivate "P2MW.S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap.F6preAux"

open F6preAux in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hfree : Module.Free 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
    (hrank : Module.finrank 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) = 2) :
    ∃ Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}),

      (∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
        Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') ∧

      (∀ (n : ℕ) (x : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), Fr₂ n (Fr₂ n x) = x) ∧

      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Finite ∧
        (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Flat) := by
  haveI := hfree

  haveI hfin : Module.Finite 𝒪 ↥(O2 Fr) := by
    rcases subsingleton_or_nontrivial 𝒪 with h𝒪 | h𝒪
    · haveI : Subsingleton ↥(O2 Fr) := Module.subsingleton 𝒪 _
      exact Module.Finite.of_finite
    · exact Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI hflat : Module.Flat 𝒪 ↥(O2 Fr) := inferInstance
  refine ⟨fun n => Fr₂lvl Fr π n, fun n y y' h => Fr₂lvl_link Fr π n y y' h, fun n x => Fr₂lvl_Fr₂lvl Fr π n x, fun n => ⟨?_, ?_⟩⟩
  ·
    change (baseMap Fr π n).Finite
    letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n) := (baseMap Fr π n).toAlgebra
    haveI : IsScalarTower 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n) :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : Module.Finite 𝒪 (↥(O2 Fr) ⧸ lvl Fr π n) := inferInstance
    exact Module.Finite.of_restrictScalars_finite 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n)
  · exact baseMap_flat Fr π n

end S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap
end P2MW
export P2MW.S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap (solution)

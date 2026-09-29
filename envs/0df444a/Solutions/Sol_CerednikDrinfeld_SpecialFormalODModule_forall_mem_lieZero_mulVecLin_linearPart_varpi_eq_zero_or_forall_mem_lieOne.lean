-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2b4a9693-4090-5d75-9a1f-2a304177f08c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Matrix

namespace DDF1

open MvPowerSeries in
theorem linearPart_comp {B : Type} [CommRing B] (ψ φ : Series B)
    (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem frob_frob {q : ℕ} [Fact q.Prime] (a : Zp2 q) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  rw [← pow_mul, ← pow_two, ← GaloisField.card q 2 two_ne_zero, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem mem_lieZero_iff {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] (j : Zp2 q →+* B)
    (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem mem_lieOne_iff {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B] (j : Zp2 q →+* B)
    (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieOne j ↔
      ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

end DDF1

open DDF1 in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharP k q]
    (j : Zp2 q →+* k) (X₀ : SpecialFormalODModule q j) :
    (∀ m ∈ X₀.toFormalODModule.lieZero j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∨
      (∀ m ∈ X₀.toFormalODModule.lieOne j, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) := by
  classical
  set X := X₀.toFormalODModule with hX
  have hcv : ∀ i, MvPowerSeries.constantCoeff (X.varpi i) = 0 := X.isLawHom_varpi.1
  have hca : ∀ a i, MvPowerSeries.constantCoeff (X.act a i) = 0 := fun a => (X.isLawHom_act a).1

  have hMM : MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart X.varpi = 0 := by
    have h := congrArg MvFormalGroup.linearPart X.varpi_comp_varpi
    rw [linearPart_comp _ _ hcv, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries] at h
    rw [h]
    ext i i'
    simp [Matrix.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero k q]

  have hMA : ∀ a, MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (X.act (WittVector.frobenius a)) * MvFormalGroup.linearPart X.varpi := by
    intro a
    have h := congrArg MvFormalGroup.linearPart (X.varpi_comp_act a)
    rwa [linearPart_comp _ _ (hca a), linearPart_comp _ _ hcv] at h

  have hmap0 : ∀ m ∈ X.lieZero j, MvFormalGroup.linearPart X.varpi *ᵥ m ∈ X.lieOne j := by
    intro m hm
    rw [mem_lieZero_iff] at hm
    rw [mem_lieOne_iff]
    intro b
    have hb : WittVector.frobenius (WittVector.frobenius b) = b := frob_frob b
    have := hMA (WittVector.frobenius b)
    rw [hb] at this
    rw [Matrix.mulVec_mulVec, ← this, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul]
  have hmap1 : ∀ m ∈ X.lieOne j, MvFormalGroup.linearPart X.varpi *ᵥ m ∈ X.lieZero j := by
    intro m hm
    rw [mem_lieOne_iff] at hm
    rw [mem_lieZero_iff]
    intro b
    have hb : WittVector.frobenius (WittVector.frobenius b) = b := frob_frob b
    have := hMA (WittVector.frobenius b)
    rw [hb] at this
    rw [Matrix.mulVec_mulVec, ← this, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, hb]

  haveI hinv : Module.Invertible k ↥(X.lieOne j) := X₀.isSpecial.2.2
  have hfin : Module.finrank k ↥(X.lieOne j) = 1 := Module.Invertible.finrank_eq_one k _
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨m₀, hm₀, hne₀⟩, ⟨m₁, hm₁, hne₁⟩⟩ := hcon
  rw [Matrix.mulVecLin_apply] at hne₀ hne₁
  have hmem : MvFormalGroup.linearPart X.varpi *ᵥ m₀ ∈ X.lieOne j := hmap0 m₀ hm₀
  have hne' : (⟨MvFormalGroup.linearPart X.varpi *ᵥ m₀, hmem⟩ : ↥(X.lieOne j)) ≠ 0 := by
    intro h0
    exact hne₀ (by simpa using congrArg Subtype.val h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne').1 hfin ⟨m₁, hm₁⟩
  have hc' : c • (MvFormalGroup.linearPart X.varpi *ᵥ m₀) = m₁ := by
    simpa using congrArg Subtype.val hc
  apply hne₁
  rw [← hc', Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMM, Matrix.zero_mulVec, smul_zero]

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_forall_mem_lieZero_mulVecLin_linearPart_varpi_eq_zero_or_forall_mem_lieOne (solution)

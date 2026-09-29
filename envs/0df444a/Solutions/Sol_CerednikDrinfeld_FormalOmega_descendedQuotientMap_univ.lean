-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8a5b20b6-8f0e-5a86-9e37-47ad8ca135e1

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_existsUnique_hom_pullback_of_natural_of_invariant
import Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedFamily_comp_frobenius_zpow_eq_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_univ

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem F6bAux_inv (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (n : ℕ)
    (Zn Xn T : Scheme.{0}) (DMq : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Zn))
    (p₁ : Xn ⟶ Zn) (p₂ : Xn ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (α : Xn ⟶ Xn) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (e : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (ρCn : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T))
    (wn : Xn ⟶ T) (hw : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ wn = ρCn B hB c P)
    (hwu : ∀ w' : Xn ⟶ T, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ w' = ρCn B hB c P) → w' = wn)
    (hPtot : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (P : (Omega K₀ π).obj B), ∃ P', DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P')
    (ha1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P P' : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ∀ x : Spec (CommRingCat.of B) ⟶ Xn, x ≫ p₁ = DMq B hB P → (x ≫ α) ≫ p₁ = DMq B hB P')
    (ha2 : α ≫ p₂ = p₂ ≫ Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom))
    (hequiv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P P' : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρCn B hB (c.comp e.toAlgHom) P' = ρCn B hB c P) :
    α ≫ wn = wn := by
  apply hwu
  intro B _ _ hB c P x hx₁ hx₂
  obtain ⟨P', hP'⟩ := hPtot B P
  have hx₁' := ha1 B hB P P' hP' x hx₁
  have hx₂' : (x ≫ α) ≫ p₂ = Spec.map (CommRingCat.ofHom ((c.comp e.toAlgHom).toRingHom)) := by
    rw [Category.assoc, ha2, ← Category.assoc, hx₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [← Category.assoc, hw B hB _ P' _ hx₁' hx₂']
  exact hequiv B hB c P P' hP'

theorem F6bAux_xt (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (n : ℕ)
    (Zn Zn1 Xn Xn1 T : Scheme.{0}) (DMq : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Zn)) (DMq1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0 → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Zn1))
    (zt : Zn ⟶ Zn1)
    (hqzt : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0)
      (P : (Omega K₀ π).obj B), DMq1 B hB' P = DMq B hB P ≫ zt)
    (p₁ : Xn ⟶ Zn) (p₂ : Xn ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (p₁' : Xn1 ⟶ Zn1) (p₂' : Xn1 ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1 + 1)})))
    (xt : Xn ⟶ Xn1) (hxt₁ : xt ≫ p₁' = p₁ ≫ zt)
    (hxt₂ : xt ≫ p₂' = p₂ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))))
    (ρCn : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T)) (ρCn1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0 → ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1 + 1)}) →ₐ[𝒪] B) → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T))
    (hρCC : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0)
      (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
      ρCn1 B hB' (c.comp (Ideal.Quotient.factorₐ 𝒪
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))) P = ρCn B hB c P)
    (wn : Xn ⟶ T) (wn1 : Xn1 ⟶ T)
    (hw1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1 + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn1), x ≫ p₁' = DMq1 B hB P → x ≫ p₂' = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ wn1 = ρCn1 B hB c P)
    (hwu : ∀ w' : Xn ⟶ T, (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ w' = ρCn B hB c P) → w' = wn) :
    xt ≫ wn1 = wn := by
  apply hwu
  intro B _ _ hB c P x hx₁ hx₂
  have hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0 := by rw [pow_succ, hB, zero_mul]
  have hx₁' : (x ≫ xt) ≫ p₁' = DMq1 B hB' P := by
    rw [Category.assoc, hxt₁, ← Category.assoc, hx₁]; exact (hqzt B hB hB' P).symm
  have hx₂' : (x ≫ xt) ≫ p₂' = Spec.map (CommRingCat.ofHom (c.comp (Ideal.Quotient.factorₐ 𝒪
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))).toRingHom) := by
    rw [Category.assoc, hxt₂, ← Category.assoc, hx₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [← Category.assoc, hw1 B hB' _ P _ hx₁' hx₂']
  exact hρCC B hB hB' c P

theorem F6bAux_qclause (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (n : ℕ)
    (Zn Xn Yn T : Scheme.{0}) (DMq : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Zn))
    (p₁ : Xn ⟶ Zn) (p₂ : Xn ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (Sn : Scheme.{0}) (zb : Zn ⟶ Sn) (s : Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ⟶ Sn) (hXn : IsPullback p₁ p₂ zb s)
    (hcompat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B), DMq B hB P ≫ zb = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ s)
    (pn : Xn ⟶ Yn) (un : Yn ⟶ T) (wn : Xn ⟶ T) (hun : pn ≫ un = wn)
    (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B) (ρ₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B) (hρ₂hon : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B), ρ₂ B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P))
    (hw : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ wn = (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1)
    (qn : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ Yn)) (hqdef : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B) (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr)) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → qn B hB (ψ, P) = x ≫ pn) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      qn B hB x ≫ un = (ρ' B ⟨n + 1, hB⟩ x).1 := by
  intro B _ _ hB x
  obtain ⟨ψ, P⟩ := x
  change Onr →ₐ[𝒪] B at ψ
  have hker : ∀ z ∈ (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}), (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val) z = 0 := by
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, map_pow, AlgHom.commutes, hB, mul_zero]
  let ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B := Ideal.Quotient.liftₐ _ (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val) hker
  have hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr) := fun y => rfl
  have hx₁ := hXn.lift_fst _ _ (hcompat B hB ψ₂ P)
  have hx₂ := hXn.lift_snd _ _ (hcompat B hB ψ₂ P)
  rw [hqdef B hB ψ ψ₂ hψ₂ P _ hx₁ hx₂, Category.assoc, hun, hw B hB ψ₂ P _ hx₁ hx₂]
  show (ρ₂ B ⟨n + 1, hB⟩ (ψ₂.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1 = (ρ' B ⟨n + 1, hB⟩ (ψ, P)).1
  rw [← hρ₂hon B ⟨n + 1, hB⟩ ψ P]
  have hcc : ψ₂.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) = ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val := AlgHom.ext fun y => rfl
  rw [hcc]

theorem F6bAux_unique
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (n : ℕ)
    (Zn Xn Yn T : Scheme.{0}) (DMq : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Zn))
    (hDMqnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
      DMq B' hB' ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ DMq B hB P)
    (p₁ : Xn ⟶ Zn) (p₂ : Xn ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (Sn : Scheme.{0}) (zb : Zn ⟶ Sn) (s : Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ⟶ Sn) (hXn : IsPullback p₁ p₂ zb s)
    (hcompat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B), DMq B hB P ≫ zb = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ s)
    (pn : Xn ⟶ Yn) (un : Yn ⟶ T)
    (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B) (ρ₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B)
    (hρ₂nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
      ρ₂ B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ₂ B hB x))
    (hρ₂hon : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B), ρ₂ B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P))
    (qn : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ Yn)) (hqdef : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B) (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr)) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → qn B hB (ψ, P) = x ≫ pn)
    (h3 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      qn B hB x ≫ un = (ρ' B ⟨n + 1, hB⟩ x).1) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DMq B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ (pn ≫ un) = (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1 := by
  intro B _ _ hB c P x hx₁ hx₂
  have key := CerednikDrinfeld.FormalOmega.eq_of_natural_of_forall_eq_of_comp_mk_eq_comp_val
    𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr n (Omega K₀ π) T
    (fun B _ _ hB c P => hXn.lift (DMq B hB P) (Spec.map (CommRingCat.ofHom c.toRingHom)) (hcompat B hB c P) ≫ pn ≫ un)
    (by
      intro B _ _ B' _ _ hB hB' φ c P
      have hL : hXn.lift (DMq B' hB' ((Omega K₀ π).map φ P)) (Spec.map (CommRingCat.ofHom (φ.comp c).toRingHom))
            (hcompat B' hB' (φ.comp c) ((Omega K₀ π).map φ P)) =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            hXn.lift (DMq B hB P) (Spec.map (CommRingCat.ofHom c.toRingHom)) (hcompat B hB c P) := by
        apply hXn.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, IsPullback.lift_fst]; exact hDMqnat B B' hB hB' φ P
        · rw [IsPullback.lift_snd, Category.assoc, IsPullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
      show _ ≫ pn ≫ un = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ _ ≫ pn ≫ un
      rw [hL, Category.assoc])
    (fun B _ _ hB c P => (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1)
    (by
      intro B _ _ B' _ _ hB hB' φ c P
      have h := congrArg Subtype.val (hρ₂nat B B' ⟨n + 1, hB⟩ ⟨n + 1, hB'⟩ φ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P))
      rw [Scheme.nilpPoints_map_val] at h
      exact h)
    (by
      intro B _ _ hB ψ c hc P
      show hXn.lift (DMq B hB P) (Spec.map (CommRingCat.ofHom c.toRingHom)) (hcompat B hB c P) ≫ pn ≫ un =
        (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1
      rw [← Category.assoc, ← hqdef B hB ψ c hc P _ (hXn.lift_fst _ _ _) (hXn.lift_snd _ _ _), h3 B hB (ψ, P),
        ← hρ₂hon B ⟨n + 1, hB⟩ ψ P]
      have hcc : c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) = ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val := AlgHom.ext fun y => hc y
      rw [hcc])
  have hxeq : x = hXn.lift (DMq B hB P) (Spec.map (CommRingCat.ofHom c.toRingHom)) (hcompat B hB c P) :=
    hXn.hom_ext (hx₁.trans (hXn.lift_fst _ _ _).symm) (hx₂.trans (hXn.lift_snd _ _ _).symm)
  subst hxeq
  exact key B hB c P

theorem F6bAux_over (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (n : ℕ) (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀))) (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (hC : (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) π) ^ (n + 1) = 0)
    (Xn T : Scheme.{0}) (p₁ : Xn ⟶ DM.Z n) (p₂ : Xn ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (s : Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))))
    (hXn : IsPullback p₁ p₂ (DM.zb n) s)
    (t : T ⟶ Spec (CommRingCat.of 𝒪)) (ρ₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B)
    (wn : Xn ⟶ T) (hw : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ Xn), x ≫ p₁ = DM.q n B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ wn = (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1)
    (xbn : Xn ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) (hxb : xbn = p₁ ≫ DM.zb n) :
    wn ≫ t = xbn ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := by
  have key := CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant
    𝒪 π K₀ r g₁ N DM n (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) hC Xn p₁ p₂ s hs hXn (Spec (CommRingCat.of 𝒪))
    (fun B _ _ hB c P => Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)))
    (by intro B _ _ B' _ _ hB hB' φ c P; exact (Scheme.specMap_algHom_comp_specOver φ).symm)
    (by intro B _ _ hB c g hg P P' h; rfl)
  refine key.unique ?_ ?_
  · intro B _ _ hB c P x hx₁ hx₂
    rw [← Category.assoc, hw B hB c P x hx₁ hx₂]
    exact (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).2
  · intro B _ _ hB c P x hx₁ hx₂
    rw [hxb, Category.assoc, ← Category.assoc x, hx₁]
    exact DM.q_over n B hB P

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0)
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)

    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] [Finite G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (θ : ↥Γ →* G₂) (Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (ha_over : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hX : ∀ n : ℕ, IsPullback (pr₁ n) (pr₂ n) (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hxb : ∀ n : ℕ, xb n = pr₁ n ≫ DM.zb n)
    (hxt₁ : ∀ n : ℕ, xt n ≫ pr₁ (n + 1) = pr₁ n ≫ DM.zt n)
    (hxt₂ : ∀ n : ℕ, xt n ≫ pr₂ (n + 1) = pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))))
    (hθsurj : Function.Surjective θ) (hθker : ∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N)
    (hFr₂ : ∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (ha_pr₂ : ∀ (n : ℕ) (γ : ↥Γ), (a n (θ γ)).hom ≫ pr₂ n =
      pr₂ n ≫ Spec.map (CommRingCat.ofHom ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom))
    (ha_pr₁ : ∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
      ∀ x : Spec (CommRingCat.of B) ⟶ X n, x ≫ pr₁ n = DM.q n B hB P → (x ≫ (a n (θ γ)).hom) ≫ pr₁ n = DM.q n B hB P')

    (DQ : TowerQuotientDatum 𝒪 π X xb xt G₂ a)
    (q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ DQ.Y n))
    (hqdef : (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B)
        (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr))
        (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X n),
        x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → q n B hB (ψ, P) = x ≫ DQ.p n))
    (hqover : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B hB x ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)))
    (hqnat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B')
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB x)
    (hqyt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q (n + 1) B hB' x = q n B hB x ≫ DQ.yt n)
    (hqinv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (γ : G), γ ∈ Γ →
    ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → q n B hB x' = q n B hB x)
    :
    ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
    ∃ u : ∀ n : ℕ, DQ.Y n ⟶ T,
      (∀ n : ℕ, u n ≫ t = DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) ∧
      (∀ n : ℕ, DQ.yt n ≫ u (n + 1) = u n) ∧
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u n = (ρ' B ⟨n + 1, hB⟩ x).1) ∧
      ∀ u' : ∀ n : ℕ, DQ.Y n ⟶ T,
        (∀ n : ℕ, u' n ≫ t = DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) →
        (∀ n : ℕ, DQ.yt n ≫ u' (n + 1) = u' n) →
        (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), q n B hB x ≫ u' n = (ρ' B ⟨n + 1, hB⟩ x).1) →
        u' = u := by
  intro T t ρ' hρ'nat hρ'inv
  classical
  obtain ⟨-, -, -, -, -, -, hPtot, -⟩ := CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws (K₀ := K₀) π Onr Fr vdet

  obtain ⟨ρ₂, hρ₂nat, hρ₂hon, hρ₂uniq⟩ :=
    CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet G σ Γ hcent
      T t ρ' hρ'nat hρ'inv
  have hU2 := fun n : ℕ => CerednikDrinfeld.FormalOmega.descendedFamily_comp_frobenius_zpow_eq_of_isPullback
      𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr K₀ vdet G σ Γ Γ' hΓ'
      T t ρ' hρ'nat hρ'inv ρ₂ hρ₂nat hρ₂hon hρ₂uniq n (Fr₂ n) (hFr₂ n)

  let ρC : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
      ((↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) → (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ T) :=
    fun n B _ _ hB c P => (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1
  have hC : ∀ n : ℕ, (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) π) ^ (n + 1) = 0 := by
    intro n
    rw [IsScalarTower.algebraMap_apply 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}), Ideal.Quotient.algebraMap_eq]
    exact (map_pow (Ideal.Quotient.mk _) _ _).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have hs : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))) := by
    intro n
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hρCnat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B),
      ρC n B' hB' (φ.comp c) ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ρC n B hB c P := by
    intro n B _ _ B' _ _ hB hB' φ c P
    have h := congrArg Subtype.val (hρ₂nat B B' ⟨n + 1, hB⟩ ⟨n + 1, hB'⟩ φ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P))
    rw [Scheme.nilpPoints_map_val] at h
    exact h
  have hρCinv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B)
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → ρC n B hB c P' = ρC n B hB c P := by
    intro n B _ _ hB c g hg P P' hPP'
    obtain ⟨γ', hγ', hγ'eq⟩ := Subgroup.mem_map.mp (hNle hg)
    exact congrArg Subtype.val ((hU2 n).2 B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))) g ⟨γ', hγ', (hρ γ').symm.trans hγ'eq⟩ P P' hPP')
  let PF : ∀ n : ℕ, (X n ⟶ T) → Prop := fun n v => ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X n),
      x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ v = ρC n B hB c P
  have hU1a : ∀ n : ℕ, ∃! w : X n ⟶ T, PF n w :=
    fun n => CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant
      𝒪 π K₀ r g₁ N DM n (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (hC n) (X n) (pr₁ n) (pr₂ n) _ (hs n) (hX n) T (ρC n) (hρCnat n) (hρCinv n)
  let w : ∀ n : ℕ, X n ⟶ T := fun n => (hU1a n).exists.choose
  have hw : ∀ n : ℕ, PF n (w n) := fun n => (hU1a n).exists.choose_spec
  have hwu : ∀ (n : ℕ) (w' : X n ⟶ T), PF n w' → w' = w n := fun n w' h => (hU1a n).unique h (hw n)

  have hcompat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (c : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
      DM.q n B hB P ≫ DM.zb n = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    intro n B _ _ hB c P
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc, Category.assoc, DM.q_over, hs n]
    exact (Scheme.specMap_algHom_comp_specOver c).symm

  have hwinv : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ w n = w n := by
    intro n g
    obtain ⟨γ, rfl⟩ := hθsurj g
    exact F6bAux_inv 𝒪 π K₀ Onr Fr n (DM.Z n) (X n) T (DM.q n) (pr₁ n) (pr₂ n) (a n (θ γ)).hom (σ (γ : G))
      ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))) (ρC n) (w n) (hw n) (hwu n)
      (fun B _ _ P => hPtot B (σ (γ : G)) P) (ha_pr₁ n γ) (ha_pr₂ n γ)
      (fun B _ _ hB c P P' h => congrArg Subtype.val ((hU2 n).1 B hB c (γ : G) γ.2 P P' h))
  have hwt : ∀ n : ℕ, w n ≫ t = xb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := fun n =>
    F6bAux_over 𝒪 π K₀ Onr Fr n r g₁ N DM (hC n) (X n) T (pr₁ n) (pr₂ n) _ (hs n) (hX n) t ρ₂ (w n) (hw n) (xb n) (hxb n)
  have hwxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n := fun n =>
    F6bAux_xt 𝒪 π K₀ Onr Fr n (DM.Z n) (DM.Z (n + 1)) (X n) (X (n + 1)) T (DM.q n) (DM.q (n + 1)) (DM.zt n) (DM.q_zt n)
      (pr₁ n) (pr₂ n) (pr₁ (n + 1)) (pr₂ (n + 1)) (xt n) (hxt₁ n) (hxt₂ n) (ρC n) (ρC (n + 1))
      (fun B _ _ hB hB' c P => by
        show (ρ₂ B ⟨n + 1 + 1, hB'⟩ (_, P)).1 = (ρ₂ B ⟨n + 1, hB⟩ (c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), P)).1
        have hcc : (c.comp (Ideal.Quotient.factorₐ 𝒪
            (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))).comp
            (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1 + 1)})) = c.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) :=
          AlgHom.ext fun y => rfl
        rw [hcc])
      (w n) (w (n + 1)) (hw (n + 1)) (hwu n)

  obtain ⟨u, hu, huu⟩ := AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq 𝒪 π X xb xt G₂ a DQ T w hwinv hwxt
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  ·
    have key := AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq 𝒪 π X xb xt G₂ a DQ (Spec (CommRingCat.of 𝒪))
      (fun n => xb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
      (fun n g => by rw [← Category.assoc, ha_over])
      (fun n => by
        rw [← Category.assoc, (hcart n).w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl)
    have e := key.unique (y₁ := fun n => u n ≫ t) (y₂ := fun n => DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
      (fun n => by rw [← Category.assoc, hu n, hwt n]) (fun n => by rw [← Category.assoc, DQ.p_over n])
    exact fun n => congrFun e n
  ·
    have e := huu (fun n => DQ.yt n ≫ u (n + 1))
      (fun n => by rw [← Category.assoc, ← DQ.p_xt n, Category.assoc, hu (n + 1), hwxt n])
    exact fun n => congrFun e n
  ·
    intro n
    exact F6bAux_qclause 𝒪 π K₀ Onr Fr n (DM.Z n) (X n) (DQ.Y n) T (DM.q n) (pr₁ n) (pr₂ n) _ (DM.zb n) _ (hX n)
      (hcompat n) (DQ.p n) (u n) (w n) (hu n) t ρ' ρ₂ hρ₂hon (hw n) (q n) (hqdef n)
  ·
    intro u' h1 h2 h3
    apply huu
    intro n
    apply hwu n
    exact F6bAux_unique 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr K₀ n
      (DM.Z n) (X n) (DQ.Y n) T (DM.q n) (DM.q_natural n) (pr₁ n) (pr₂ n) _ (DM.zb n) _ (hX n) (hcompat n) (DQ.p n) (u' n)
      t ρ' ρ₂ hρ₂nat hρ₂hon (q n) (hqdef n) (h3 n)

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_univ
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_univ (solution)

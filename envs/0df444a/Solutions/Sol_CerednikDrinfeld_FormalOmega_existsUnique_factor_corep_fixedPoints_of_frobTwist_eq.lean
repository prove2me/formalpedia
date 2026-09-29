-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_of_frobTwist_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ea3524eb-08e2-555d-9913-1e9b91c28b34

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_of_frobTwist_eq

set_option autoImplicit false

open scoped NumberField
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega
open AlgebraicGeometry
open scoped TensorProduct

namespace G2Aux

section
variable (𝒪 : Type) [CommRing 𝒪] (E : Type) [CommRing E] [Algebra 𝒪 E] (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  [Algebra E Onr] [IsScalarTower 𝒪 E Onr]
  (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra E C] [IsScalarTower 𝒪 E C]

noncomputable def incl : C →ₐ[𝒪] C ⊗[E] Onr :=
  (Algebra.TensorProduct.includeLeft : C →ₐ[E] C ⊗[E] Onr).restrictScalars 𝒪

noncomputable def psiInf : Onr →ₐ[𝒪] C ⊗[E] Onr :=
  (Algebra.TensorProduct.includeRight : Onr →ₐ[E] C ⊗[E] Onr).restrictScalars 𝒪

theorem incl_apply (c : C) : incl 𝒪 E Onr C c = c ⊗ₜ 1 := rfl
theorem psiInf_apply (x : Onr) : psiInf 𝒪 E Onr C x = 1 ⊗ₜ x := rfl
theorem incl_toRingHom : (incl 𝒪 E Onr C).toRingHom = Algebra.TensorProduct.includeLeftRingHom := rfl

noncomputable def sig (FrS : Onr ≃ₐ[E] Onr) : C ⊗[E] Onr →ₐ[𝒪] C ⊗[E] Onr :=
  (Algebra.TensorProduct.map (AlgHom.id E C) (FrS : Onr →ₐ[E] Onr)).restrictScalars 𝒪

theorem sig_toRingHom (FrS : Onr ≃ₐ[E] Onr) :
    (sig 𝒪 E Onr C FrS).toRingHom = (Algebra.TensorProduct.map (AlgHom.id E C) (FrS : Onr →ₐ[E] Onr)).toRingHom := rfl

theorem sig_tmul (FrS : Onr ≃ₐ[E] Onr) (c : C) (x : Onr) : sig 𝒪 E Onr C FrS (c ⊗ₜ x) = c ⊗ₜ FrS x := by
  show Algebra.TensorProduct.map (AlgHom.id E C) (FrS : Onr →ₐ[E] Onr) (c ⊗ₜ x) = c ⊗ₜ FrS x
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem sig_comp_incl (FrS : Onr ≃ₐ[E] Onr) : (sig 𝒪 E Onr C FrS).comp (incl 𝒪 E Onr C) = incl 𝒪 E Onr C := by
  apply AlgHom.ext; intro c
  show sig 𝒪 E Onr C FrS (c ⊗ₜ 1) = c ⊗ₜ 1
  rw [sig_tmul, map_one]

theorem sig_psiInf (FrS : Onr ≃ₐ[E] Onr) (x : Onr) : sig 𝒪 E Onr C FrS (psiInf 𝒪 E Onr C x) = psiInf 𝒪 E Onr C (FrS x) := by
  rw [psiInf_apply, psiInf_apply, sig_tmul]

noncomputable def retr (ψ : Onr →ₐ[𝒪] C) (hψ : ∀ e : E, ψ (algebraMap E Onr e) = algebraMap E C e) : C ⊗[E] Onr →ₐ[𝒪] C :=
  (Algebra.TensorProduct.lift (AlgHom.id E C) (⟨ψ.toRingHom, hψ⟩ : Onr →ₐ[E] C) (fun _ _ => Commute.all _ _)).restrictScalars 𝒪

theorem retr_tmul (ψ : Onr →ₐ[𝒪] C) (hψ : ∀ e : E, ψ (algebraMap E Onr e) = algebraMap E C e) (c : C) (x : Onr) :
    retr 𝒪 E Onr C ψ hψ (c ⊗ₜ x) = c * ψ x := by
  show Algebra.TensorProduct.lift (AlgHom.id E C) (⟨ψ.toRingHom, hψ⟩ : Onr →ₐ[E] C) (fun _ _ => Commute.all _ _) (c ⊗ₜ x) = c * ψ x
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

theorem retr_comp_incl (ψ : Onr →ₐ[𝒪] C) (hψ : ∀ e : E, ψ (algebraMap E Onr e) = algebraMap E C e) :
    (retr 𝒪 E Onr C ψ hψ).comp (incl 𝒪 E Onr C) = AlgHom.id 𝒪 C := by
  apply AlgHom.ext; intro c
  show retr 𝒪 E Onr C ψ hψ (c ⊗ₜ 1) = c
  rw [retr_tmul, map_one, mul_one]

theorem retr_comp_psiInf (ψ : Onr →ₐ[𝒪] C) (hψ : ∀ e : E, ψ (algebraMap E Onr e) = algebraMap E C e) :
    (retr 𝒪 E Onr C ψ hψ).comp (psiInf 𝒪 E Onr C) = ψ := by
  apply AlgHom.ext; intro x
  show retr 𝒪 E Onr C ψ hψ (1 ⊗ₜ x) = ψ x
  rw [retr_tmul, one_mul]

variable (C' : Type) [CommRing C'] [Algebra 𝒪 C'] [Algebra E C'] [IsScalarTower 𝒪 E C']

noncomputable def mapInf (φ : C →ₐ[𝒪] C') (hφ : ∀ e : E, φ (algebraMap E C e) = algebraMap E C' e) :
    C ⊗[E] Onr →ₐ[𝒪] C' ⊗[E] Onr :=
  (Algebra.TensorProduct.map (⟨φ.toRingHom, hφ⟩ : C →ₐ[E] C') (AlgHom.id E Onr)).restrictScalars 𝒪

theorem mapInf_tmul (φ : C →ₐ[𝒪] C') (hφ : ∀ e : E, φ (algebraMap E C e) = algebraMap E C' e) (c : C) (x : Onr) :
    mapInf 𝒪 E Onr C C' φ hφ (c ⊗ₜ x) = φ c ⊗ₜ x := by
  show Algebra.TensorProduct.map (⟨φ.toRingHom, hφ⟩ : C →ₐ[E] C') (AlgHom.id E Onr) (c ⊗ₜ x) = φ c ⊗ₜ x
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem mapInf_comp_incl (φ : C →ₐ[𝒪] C') (hφ : ∀ e : E, φ (algebraMap E C e) = algebraMap E C' e) :
    (mapInf 𝒪 E Onr C C' φ hφ).comp (incl 𝒪 E Onr C) = (incl 𝒪 E Onr C').comp φ := by
  apply AlgHom.ext; intro c
  show mapInf 𝒪 E Onr C C' φ hφ (c ⊗ₜ 1) = φ c ⊗ₜ 1
  rw [mapInf_tmul]

theorem mapInf_comp_psiInf (φ : C →ₐ[𝒪] C') (hφ : ∀ e : E, φ (algebraMap E C e) = algebraMap E C' e) :
    (mapInf 𝒪 E Onr C C' φ hφ).comp (psiInf 𝒪 E Onr C) = psiInf 𝒪 E Onr C' := by
  apply AlgHom.ext; intro x
  show mapInf 𝒪 E Onr C C' φ hφ (1 ⊗ₜ x) = 1 ⊗ₜ x
  rw [mapInf_tmul, map_one]

theorem mapInf_comp_sig (FrS : Onr ≃ₐ[E] Onr) (φ : C →ₐ[𝒪] C') (hφ : ∀ e : E, φ (algebraMap E C e) = algebraMap E C' e) :
    (mapInf 𝒪 E Onr C C' φ hφ).comp (sig 𝒪 E Onr C FrS) = (sig 𝒪 E Onr C' FrS).comp (mapInf 𝒪 E Onr C C' φ hφ) := by
  apply AlgHom.ext; intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    show mapInf 𝒪 E Onr C C' φ hφ (sig 𝒪 E Onr C FrS (c ⊗ₜ x)) = sig 𝒪 E Onr C' FrS (mapInf 𝒪 E Onr C C' φ hφ (c ⊗ₜ x))
    rw [sig_tmul, mapInf_tmul, mapInf_tmul, sig_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem incl_algebraMap_eq (e : E) : incl 𝒪 E Onr C (algebraMap E C e) = psiInf 𝒪 E Onr C (algebraMap E Onr e) := by
  rw [incl_apply, psiInf_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul]

end

end G2Aux

namespace G2Lem

theorem nilp_of {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (B : Type) [CommRing B] [Algebra 𝒪 B] (C : Type) [CommRing C] [Algebra 𝒪 C]
    (φ : B →ₐ[𝒪] C) (h : IsNilpotent (algebraMap 𝒪 B π)) : IsNilpotent (algebraMap 𝒪 C π) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [← φ.commutes, ← map_pow, hk, map_zero]⟩

theorem rho_nat1
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (C : Type) [CommRing C] [Algebra 𝒪 C]
    (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (hC : IsNilpotent (algebraMap 𝒪 C π)) (φ : B →ₐ[𝒪] C) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ρ B hB₀ x).1 = (ρ C hC ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x)).1 := by
  rw [hρ_nat B C hB₀ hC φ x]
  rfl

theorem sigma_inv
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
    (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C) :
    Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 := by
  rw [← G2Aux.sig_toRingHom 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS,
    rho_nat1 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv _ _ _ (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC) (G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS)]
  have e1 : (G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS).comp (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) =
      frobTwist Onr Fr (m : ℤ) (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) := by
    apply AlgHom.ext; intro x
    show G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C x) = G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ((Fr ^ (m : ℤ)) x)
    rw [G2Aux.sig_psiInf, hFrS]
  have e2 : Y.map (G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS) (Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y) = Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y := by
    rw [← Y.map_comp, G2Aux.sig_comp_incl]
  show (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) _ ((G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS).comp (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C),
    Y.map (G2Aux.sig 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C FrS) (Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y))).1 = _
  rw [e1, e2, hρ_inv]

theorem desc
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
    (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C) :
    ∃ g : Spec (CommRingCat.of C) ⟶ T, Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 ∧
      ∀ g' : Spec (CommRingCat.of C) ⟶ T, Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g' = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 → g' = g := by
  obtain ⟨g, hg, huniq⟩ := CerednikDrinfeld.FormalOmega.existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max
    hOnr_alg hOnr_closed hFr m hm FrS hFrS C hC T (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 (sigma_inv 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv FrS hFrS C hC y)
  refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
  · rw [G2Aux.incl_toRingHom]; exact hg
  · rw [G2Aux.incl_toRingHom] at hg'; exact hg'

theorem desc_over
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
    (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C)
    (g : Spec (CommRingCat.of C) ⟶ T) (hg : Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1) :
    g ≫ t = Scheme.specOver (𝒪 := 𝒪) C := by
  have hinvt := congrArg (fun h => h ≫ t) (sigma_inv 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv FrS hFrS C hC y)
  simp only [Category.assoc] at hinvt
  obtain ⟨g0, -, huniq0⟩ := CerednikDrinfeld.FormalOmega.existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max
    hOnr_alg hOnr_closed hFr m hm FrS hFrS C hC (Spec (CommRingCat.of 𝒪)) _ hinvt
  have a1 : g ≫ t = g0 := by
    apply huniq0
    rw [← G2Aux.incl_toRingHom 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, ← Category.assoc, hg]
  have a2 : Scheme.specOver (𝒪 := 𝒪) C = g0 := by
    apply huniq0
    have h2 := (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
      (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).2
    rw [h2, ← G2Aux.incl_toRingHom 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C]
    exact Scheme.specMap_algHom_comp_specOver (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C)
  rw [a1, a2]

theorem nat_aux
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (gd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C],
      IsNilpotent (algebraMap 𝒪 C π) → Y.obj C → (Spec (CommRingCat.of C) ⟶ T))
    (hgd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ gd C hC y = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1)
    (hgd_uniq : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C) (g' : Spec (CommRingCat.of C) ⟶ T), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g' = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 → g' = gd C hC y)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (C' : Type) [CommRing C'] [Algebra 𝒪 C']
    (hC : IsNilpotent (algebraMap 𝒪 C π)) (hC' : IsNilpotent (algebraMap 𝒪 C' π)) (φ : C →ₐ[𝒪] C') (p : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj C) :
    letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).toRingHom.toAlgebra
    haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).commutes r).symm)
    letI instC' : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C' := (φ.comp (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1)).toRingHom.toAlgebra
    haveI towC' : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C' := IsScalarTower.of_algebraMap_eq (fun r => ((φ.comp (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1)).commutes r).symm)
    gd C' hC' (Y.map φ p.2) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ gd C hC p.2 := by
  letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).toRingHom.toAlgebra
  haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).commutes r).symm)
  letI instC' : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C' := (φ.comp (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1)).toRingHom.toAlgebra
  haveI towC' : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C' := IsScalarTower.of_algebraMap_eq (fun r => ((φ.comp (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1)).commutes r).symm)
  symm
  apply hgd_uniq C' hC' (Y.map φ p.2)
  have hφ : ∀ e : ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), φ (algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C e) = algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C' e := fun e => rfl
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have sq : (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C').toRingHom.comp φ.toRingHom =
      (G2Aux.mapInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C C' φ hφ).toRingHom.comp (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom :=
    congrArg AlgHom.toRingHom (G2Aux.mapInf_comp_incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C C' φ hφ).symm
  rw [sq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hgd C hC p.2,
    rho_nat1 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv _ _ _ (G2Lem.nilp_of π C' _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C') hC') (G2Aux.mapInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C C' φ hφ)]
  congr 2
  show ((G2Aux.mapInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C C' φ hφ).comp (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C),
      Y.map (G2Aux.mapInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C C' φ hφ) (Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) p.2)) =
    (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C', Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C') (Y.map φ p.2))
  rw [G2Aux.mapInf_comp_psiInf, ← Y.map_comp, ← Y.map_comp, G2Aux.mapInf_comp_incl]

theorem fac_aux
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (gd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C],
      IsNilpotent (algebraMap 𝒪 C π) → Y.obj C → (Spec (CommRingCat.of C) ⟶ T))
    (hgd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ gd C hC y = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1)
    (hgd_uniq : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C) (g' : Spec (CommRingCat.of C) ⟶ T), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g' = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 → g' = gd C hC y)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C) (y : Y.obj C) :
    letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val).toRingHom.toAlgebra
    haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val).commutes r).symm)
    (ρ C hC (ψ, y)).1 = gd C hC y := by
  letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val).toRingHom.toAlgebra
  haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val).commutes r).symm)
  have hψ : ∀ e : ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ (algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr e) = algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C e := fun e => rfl
  have key := hgd C hC y
  have key2 := congrArg (fun h => Spec.map (CommRingCat.ofHom (G2Aux.retr 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ).toRingHom) ≫ h) key
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at key2
  have r1 : (G2Aux.retr 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ).toRingHom.comp (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom = RingHom.id C :=
    congrArg AlgHom.toRingHom (G2Aux.retr_comp_incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ)
  rw [r1, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at key2
  rw [key2, rho_nat1 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv _ _ _ hC (G2Aux.retr 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ)]
  congr 2
  show (ψ, y) = ((G2Aux.retr 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ).comp (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C),
    Y.map (G2Aux.retr 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C ψ hψ) (Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y))
  rw [G2Aux.retr_comp_psiInf, ← Y.map_comp, G2Aux.retr_comp_incl, Y.map_id]

theorem uniq_aux
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y))
    (gd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C],
      IsNilpotent (algebraMap 𝒪 C π) → Y.obj C → (Spec (CommRingCat.of C) ⟶ T))
    (hgd : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ gd C hC y = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1)
    (hgd_uniq : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C) (g' : Spec (CommRingCat.of C) ⟶ T), Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ g' = (ρ (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC)
            (G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) y)).1 → g' = gd C hC y)
    (ρbar' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hnat' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B), ρbar' B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρbar' B hB x))
    (hfac' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
          ρ B hB (ψ, y) = ρbar' B hB (ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, y))
    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (p : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj C) :
    letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).toRingHom.toAlgebra
    haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).commutes r).symm)
    (ρbar' C hC p).1 = gd C hC p.2 := by
  letI instC : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).toRingHom.toAlgebra
  haveI towC : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).commutes r).symm)
  apply hgd_uniq C hC p.2
  have n1 := congrArg Subtype.val (hnat' C (C ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) hC (G2Lem.nilp_of π C _ (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) hC) (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) p)
  change _ = Spec.map (CommRingCat.ofHom (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).toRingHom) ≫ (ρbar' C hC p).1 at n1
  rw [← n1, hfac']
  congr 2
  show ((G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).comp p.1, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) p.2) =
    ((G2Aux.psiInf 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C).comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, Y.map (G2Aux.incl 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C) p.2)
  congr 1
  apply AlgHom.ext; intro e
  exact G2Aux.incl_algebraMap_eq 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr C e

end G2Lem

theorem solution
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
    (m : ℕ) (hm : 0 < m)
    (Y : AlgFunctor 𝒪) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B → (Scheme.nilpPoints t).obj B)
    (hρ_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) Y).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x))
    (hρ_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
      ρ B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρ B hB (ψ, y)) :

    ∃ ρbar : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B → (Scheme.nilpPoints t).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B), ρbar B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρbar B hB x)) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
        ρ B hB (ψ, y) = ρbar B hB (ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, y)) ∧
      ∀ ρbar' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B), ρbar' B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).map φ x) = (Scheme.nilpPoints t).map φ (ρbar' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (y : Y.obj B),
          ρ B hB (ψ, y) = ρbar' B hB (ψ.comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, y)) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) Y).obj B), ρbar' B hB x = ρbar B hB x := by
  classical
  obtain ⟨FrS, hFrS⟩ : ∃ FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr, ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x :=
    ⟨AlgEquiv.ofRingEquiv (f := ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr ≃+* Onr))
      (fun e => (AlgHom.mem_equalizer _ _ _).mp e.2), fun x => rfl⟩
  have hdesc := G2Lem.desc 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv FrS hFrS
  choose gd hgd hgd_uniq using hdesc
  have hover : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C]
      (hC : IsNilpotent (algebraMap 𝒪 C π)) (y : Y.obj C), gd C hC y ≫ t = Scheme.specOver (𝒪 := 𝒪) C :=
    fun C _ _ _ _ hC y => G2Lem.desc_over 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv FrS hFrS C hC y (gd C hC y) (hgd C hC y)
  refine ⟨fun C _ _ hC p => by
      letI instE : Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := (show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).toRingHom.toAlgebra
      haveI towE : IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) C := IsScalarTower.of_algebraMap_eq (fun r => ((show ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) →ₐ[𝒪] C from p.1).commutes r).symm)
      exact ⟨gd C hC p.2, hover C hC p.2⟩, ?_, ?_, ?_⟩
  · intro C _ _ C' _ _ hC hC' φ p
    apply Subtype.ext
    exact G2Lem.nat_aux 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv gd hgd hgd_uniq C C' hC hC' φ p
  · intro C _ _ hC ψ y
    apply Subtype.ext
    exact G2Lem.fac_aux 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv gd hgd hgd_uniq C hC ψ y
  · intro ρbar' hnat' hfac' C _ _ hC p
    apply Subtype.ext
    exact G2Lem.uniq_aux 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr m hm Y T t ρ hρ_nat hρ_inv gd hgd hgd_uniq ρbar' hnat' hfac' C hC p

end S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_of_frobTwist_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_of_frobTwist_eq (solution)

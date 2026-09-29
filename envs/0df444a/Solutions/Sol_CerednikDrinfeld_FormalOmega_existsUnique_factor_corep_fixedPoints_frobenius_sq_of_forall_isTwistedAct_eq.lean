-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e6b7b208-3c8a-5594-b46e-52a4e563ca9d

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_of_frobTwist_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

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
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))

    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B)
    (hρ'nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x))
    (hρ'inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) :
    ∃ ρ₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B,

      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
        ρ₂ B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ₂ B hB x)) ∧

      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
        ρ₂ B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P)) ∧

      ∀ ρ₂' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
          ρ₂' B' hB' ((AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ₂' B hB x)) →
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
          ρ₂' B hB (ψ.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val, P) = ρ' B hB (ψ, P)) →
        ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (Omega K₀ π)).obj B),
          ρ₂' B hB x = ρ₂ B hB x := by
  classical

  obtain ⟨z, hzΓ, c, hzc, hzv⟩ := hcent
  have hc0 : c ≠ 0 := by
    intro hc
    have hdet : ((Matrix.GeneralLinearGroup.det (σ z) : K₀ˣ) : K₀) = 0 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hzc, hc, zero_smul, Matrix.det_zero]
    exact (Matrix.GeneralLinearGroup.det (σ z)).ne_zero hdet
  have hσz : σ z = scalarGL (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hzc, scalarGL_coe, Units.val_mk0]
  have hfix : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (P : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B (σ z)⁻¹ P P := by
    intro B _ _ P
    have h := CerednikDrinfeld.FormalOmega.Omega.action_scalarGL (K := K₀) π B (Units.mk0 c hc0) P
    rw [← hσz] at h
    have h' := DeligneDatum.isPullback_pullback (K := K₀) π B (σ z)⁻¹ P
    exact (congrArg (DeligneDatum.IsPullback (K := K₀) (π := π) B (σ z)⁻¹ P) h).mp h'
  have htw : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet (σ z))) (frobTwist Onr Fr ((2 : ℕ) : ℤ) ψ) = ψ := by
    intro B _ _ ψ
    rw [hzv, toAdd_ofAdd]
    apply AlgHom.ext
    intro x
    show ψ ((Fr ^ ((2 : ℕ) : ℤ)) ((Fr ^ (-(2 : ℤ))) x)) = ψ x
    rw [← AlgEquiv.mul_apply, ← zpow_add]
    norm_num
  have hinv2 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
      (y : (Omega K₀ π).obj B), ρ' B hB (frobTwist Onr Fr ((2 : ℕ) : ℤ) ψ, y) = ρ' B hB (ψ, y) := by
    intro B _ _ hB ψ y
    exact (hρ'inv B hB z hzΓ (frobTwist Onr Fr ((2 : ℕ) : ℤ) ψ, y) (ψ, y) ⟨(htw B ψ).symm, hfix B y⟩).symm

  obtain ⟨ρbar, hnat, hfac, huniq⟩ :=
    CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_of_frobTwist_eq
      𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr 2 two_pos
      (Omega K₀ π) T t ρ' hρ'nat hinv2

  have hS : (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) = (AlgHom.equalizer ((Fr ^ ((2 : ℕ) : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) := by
    have hFF : (Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) = Fr ^ ((2 : ℕ) : ℤ) := by
      rw [zpow_natCast, pow_two, AlgEquiv.aut_mul]
    rw [hFF]
  rw [hS]
  exact ⟨ρbar, hnat, fun B _ _ hB ψ P => (hfac B hB ψ P).symm,
    fun ρ₂' h1 h2 => huniq ρ₂' h1 (fun B _ _ hB ψ P => (h2 B hB ψ P).symm)⟩

end S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_frobenius_sq_of_forall_isTwistedAct_eq (solution)

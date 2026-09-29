-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/982a3412-498b-5074-90c2-db22285d1659

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace OmegaLaws29

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

theorem eq_pullback_of_isPullback {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (P P' : DeligneDatum (K := K₀) π B) (h : DeligneDatum.IsPullback (K := K₀) (π := π) B g P P') :
    P' = DeligneDatum.pullback π B g P := by
  apply DeligneDatum.ext'
  funext M
  exact h M

theorem isPullback_iff {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (P P' : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g P P' ↔ P' = DeligneDatum.pullback π B g P :=
  ⟨eq_pullback_of_isPullback π g P P', fun h => h ▸ DeligneDatum.isPullback_pullback π B g P⟩

theorem pullback_one_inv {B : Type} [CommRing B] [Algebra 𝒪 B] (P : DeligneDatum (K := K₀) π B) :
    DeligneDatum.pullback π B (1 : Matrix.GeneralLinearGroup (Fin 2) K₀)⁻¹ P = P :=
  (Omega.action K₀ π).act_one B P

theorem pullback_mul_inv {B : Type} [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (P : DeligneDatum (K := K₀) π B) :
    DeligneDatum.pullback π B (g' * g)⁻¹ P = DeligneDatum.pullback π B g'⁻¹ (DeligneDatum.pullback π B g⁻¹ P) :=
  (Omega.action K₀ π).act_mul B g' g P

theorem frobTwist_frobTwist {B : Type} [CommRing B] [Algebra 𝒪 B] (m n : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr m (frobTwist Onr Fr n ψ) = frobTwist Onr Fr (n + m) ψ := by
  apply AlgHom.ext
  intro x
  show ψ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) ((Fr ^ m : Onr ≃ₐ[𝒪] Onr) x)) = ψ ((Fr ^ (n + m) : Onr ≃ₐ[𝒪] Onr) x)
  rw [zpow_add, AlgEquiv.mul_apply]

theorem frobTwist_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : frobTwist Onr Fr 0 ψ = ψ := by
  apply AlgHom.ext
  intro x
  show ψ ((Fr ^ (0 : ℤ) : Onr ≃ₐ[𝒪] Onr) x) = ψ x
  rw [zpow_zero, AlgEquiv.one_apply]

theorem frobTwist_comp {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (n : ℤ)
    (ψ : Onr →ₐ[𝒪] B) : φ.comp (frobTwist Onr Fr n ψ) = frobTwist Onr Fr n (φ.comp ψ) := rfl

theorem frobTwist_vdet_mul (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (ψ : Onr →ₐ[𝒪] B) :
    frobTwist Onr Fr (- Multiplicative.toAdd (vdet (g' * g))) ψ =
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet g')) (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) ψ) := by
  rw [frobTwist_frobTwist, map_mul, toAdd_mul]
  congr 1
  ring

end OmegaLaws29

open OmegaLaws29

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' x'' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B g x x'' → x' = x'') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ∃ x', OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), OmegaNr.IsTwistedAct π Onr Fr vdet B 1 x x) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (x y z : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x y → OmegaNr.IsTwistedAct π Onr Fr vdet B g' y z →
      OmegaNr.IsTwistedAct π Onr Fr vdet B (g' * g) x z) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B' g ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x')) ∧

    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (ψ : Onr →ₐ[𝒪] B),
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet (g' * g))) ψ =
        frobTwist Onr Fr (- Multiplicative.toAdd (vdet g')) (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) ψ)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (P : (Omega K₀ π).obj B),
      ∃ P', DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (P P' P'' : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → DeligneDatum.IsPullback (K := K₀) (π := π) B g'⁻¹ P' P'' →
      DeligneDatum.IsPullback (K := K₀) (π := π) B (g' * g)⁻¹ P P'') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro B _ _ g x x' x'' h' h''
    obtain ⟨h1', h2'⟩ := h'
    obtain ⟨h1'', h2''⟩ := h''
    apply Prod.ext
    · rw [h1', h1'']
    · rw [eq_pullback_of_isPullback π _ _ _ h2', eq_pullback_of_isPullback π _ _ _ h2'']
  ·
    intro B _ _ g x
    exact ⟨(frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1, DeligneDatum.pullback π B g⁻¹ x.2), rfl,
      DeligneDatum.isPullback_pullback π B g⁻¹ x.2⟩
  ·
    intro B _ _ x
    refine ⟨?_, ?_⟩
    · rw [map_one, show Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 from rfl, neg_zero, frobTwist_zero]
    · rw [isPullback_iff, pullback_one_inv]
  ·
    intro B _ _ g g' x y z hxy hyz
    obtain ⟨h1, h2⟩ := hxy
    obtain ⟨h1', h2'⟩ := hyz
    refine ⟨?_, ?_⟩
    · rw [h1', h1, ← frobTwist_vdet_mul]
    · rw [isPullback_iff, pullback_mul_inv, ← eq_pullback_of_isPullback π _ _ _ h2, ← eq_pullback_of_isPullback π _ _ _ h2']
  ·
    intro B _ _ B' _ _ φ g x x' h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · show φ.comp x'.1 = frobTwist Onr Fr _ (φ.comp x.1)
      rw [h1]; rfl
    · show DeligneDatum.IsPullback (K := K₀) (π := π) B' g⁻¹ (DeligneDatum.map π φ x.2) (DeligneDatum.map π φ x'.2)
      rw [isPullback_iff, eq_pullback_of_isPullback π _ _ _ h2, DeligneDatum.map_pullback]
  ·
    intro B _ _ g g' ψ
    exact frobTwist_vdet_mul Onr Fr vdet g g' ψ
  ·
    intro B _ _ g P
    exact ⟨DeligneDatum.pullback π B g⁻¹ P, DeligneDatum.isPullback_pullback π B g⁻¹ P⟩
  ·
    intro B _ _ g g' P P' P'' h h'
    rw [isPullback_iff, pullback_mul_inv, ← eq_pullback_of_isPullback π _ _ _ h, ← eq_pullback_of_isPullback π _ _ _ h']

end S_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws (solution)

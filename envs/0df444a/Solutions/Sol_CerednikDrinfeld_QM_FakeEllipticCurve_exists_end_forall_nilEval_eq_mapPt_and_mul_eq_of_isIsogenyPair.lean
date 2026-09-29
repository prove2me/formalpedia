-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/568cb6a0-3832-5b46-8b95-258709fe99c7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (X₀ : FormalODModule r k₀)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (d : ℕ) (hd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (e e' : A₀.A ⟶ A₀.A) (hee' : FakeEllipticCurve.IsIsogenyPair (r ^ d) A₀ A₀ e e')
    (he : e ≫ A₀.f = A₀.f) (he' : e' ≫ A₀.f = A₀.f)
    (ε : MvFormalGroup.End X₀.F)
    (hε : ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) = mapPt e he (θ₀ B' s)) :
    ∃ ε' : MvFormalGroup.End X₀.F,
      (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt e' he' (θ₀ B' s)) ∧
      ∀ δ : MvFormalGroup.End X₀.F,
        (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            θ₀ B' (fun i => MvFormalGroup.nilEval m (δ.toPowerSeries i) s) =
              mapPt (A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩) (A₀.act_over _) (θ₀ B' s)) →
        ε' * ε = δ ∧ ε * ε' = δ := by
  classical
  obtain ⟨he₁, he'₁, hhe, hhe', -, -, hcomp⟩ := hee'
  obtain ⟨hc₁, hc₂⟩ := hcomp hd

  have germ := fun (h : A₀.A ⟶ A₀.A) (hh : h ≫ A₀.f = A₀.f)
      (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        (A₀.L.mul t P Q).1 ≫ h =
          (A₀.L.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh, P.2]⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh, Q.2]⟩).1) =>
    GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
      A₀.L A₀.L X₀.F X₀.F θ₀ θ₀ hA₀.1 hA₀.1 h hh hhom

  have hhom' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      (A₀.L.mul t P Q).1 ≫ e' =
        (A₀.L.mul t ⟨P.1 ≫ e', by rw [Category.assoc, he', P.2]⟩ ⟨Q.1 ≫ e', by rw [Category.assoc, he', Q.2]⟩).1 :=
    fun t P Q => congrArg Subtype.val (hhe' t P Q)
  have hhomact : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      (A₀.L.mul t P Q).1 ≫ A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩ =
        (A₀.L.mul t ⟨P.1 ≫ A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩, by rw [Category.assoc, A₀.act_over, P.2]⟩
          ⟨Q.1 ≫ A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩, by rw [Category.assoc, A₀.act_over, Q.2]⟩).1 :=
    fun t P Q => congrArg Subtype.val (A₀.act_hom _ t P Q)
  obtain ⟨ε', hε', -⟩ := germ e' he' hhom'
  obtain ⟨τ, -, hτu⟩ := germ (A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩) (A₀.act_over _) hhomact
  refine ⟨ε', ?_, ?_⟩
  · intro B' _ _ J m hJ s hs
    apply Subtype.ext
    rw [mapPt_coe]
    exact (hε' B' J m hJ s hs).symm
  · intro δ hδ

    have hprod : ∀ (φ ψ : MvFormalGroup.End X₀.F) (u v : A₀.A ⟶ A₀.A) (hu : u ≫ A₀.f = A₀.f) (hv : v ≫ A₀.f = A₀.f),
        (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            θ₀ B' (fun i => MvFormalGroup.nilEval m (φ.toPowerSeries i) s) = mapPt u hu (θ₀ B' s)) →
        (∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            θ₀ B' (fun i => MvFormalGroup.nilEval m (ψ.toPowerSeries i) s) = mapPt v hv (θ₀ B' s)) →
        ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
          ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
            (θ₀ B' s).1 ≫ (u ≫ v) = (θ₀ B' (fun i => MvFormalGroup.nilEval m ((ψ * φ).toPowerSeries i) s)).1 := by
      intro φ ψ u v hu hv hφ hψ B' _ _ J m hJ s hs
      have hsub := MvFormalGroup.nilEval_subst_of_mem J m hJ s hs φ.toPowerSeries φ.constantCoeff_eq_zero
      have e1 : (fun i => MvFormalGroup.nilEval m ((ψ * φ).toPowerSeries i) s) =
          fun i => MvFormalGroup.nilEval m (ψ.toPowerSeries i) (fun j => MvFormalGroup.nilEval m (φ.toPowerSeries j) s) := by
        funext i
        rw [MvFormalGroup.End.toPowerSeries_mul]
        exact (hsub (ψ.toPowerSeries i)).2
      rw [e1, hψ B' J m hJ _ (hsub (ψ.toPowerSeries 0)).1, hφ B' J m hJ s hs]
      simp only [mapPt_coe, Category.assoc]
    have hδ' : ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          (θ₀ B' s).1 ≫ A₀.act ⟨((r ^ d : ℕ) : ℚ), hd⟩ =
            (θ₀ B' (fun i => MvFormalGroup.nilEval m (δ.toPowerSeries i) s)).1 := by
      intro B' _ _ J m hJ s hs
      rw [hδ B' J m hJ s hs, mapPt_coe]
    have hε'' : ∀ (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
          θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt e' he' (θ₀ B' s) := by
      intro B' _ _ J m hJ s hs
      apply Subtype.ext
      rw [mapPt_coe]
      exact (hε' B' J m hJ s hs).symm
    have h1 := hprod ε ε' e e' he he' hε hε''
    have h2 := hprod ε' ε e' e he' he hε'' hε
    rw [hc₁] at h1
    rw [hc₂] at h2
    exact ⟨(hτu _ h1).trans (hτu _ hδ').symm, (hτu _ h2).trans (hτu _ hδ').symm⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_end_forall_nilEval_eq_mapPt_and_mul_eq_of_isIsogenyPair (solution)

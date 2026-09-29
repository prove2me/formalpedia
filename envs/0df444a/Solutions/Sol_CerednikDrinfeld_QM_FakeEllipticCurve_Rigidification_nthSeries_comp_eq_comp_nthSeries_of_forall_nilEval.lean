-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9fa59aa2-6442-5a2d-8267-c9bac519dc28

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace SLinAux

theorem nilEval_map_of_algebraMap_eq {R S B'' : Type} [CommRing R] [CommRing S] [CommRing B''] [Algebra R B''] [Algebra S B'']
    (ψ : R →+* S) (h : algebraMap R B'' = (algebraMap S B'').comp ψ) {σ : Type} [Fintype σ] [DecidableEq σ]
    (n : ℕ) (φ : MvPowerSeries σ R) (a : σ → B'') :
    MvFormalGroup.nilEval n (MvPowerSeries.map ψ φ) a = MvFormalGroup.nilEval n φ a := by
  unfold MvFormalGroup.nilEval
  have htr : MvPowerSeries.trunc' S (Finsupp.equivFunOnFinite.symm fun _ => n) (MvPowerSeries.map ψ φ) =
      MvPolynomial.map ψ (MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm fun _ => n) φ) := by
    ext m
    rw [MvPowerSeries.coeff_trunc', MvPolynomial.coeff_map, MvPowerSeries.coeff_trunc']
    split_ifs with hm
    · exact MvPowerSeries.coeff_map _ _ _
    · exact (map_zero ψ).symm
  rw [htr, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← h]

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem act_comp_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
    {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g) (x : ↥Λ) : E'.act x ≫ g = g ≫ E.act x := by
  obtain ⟨_, -, hact, -⟩ := h
  exact hact x

theorem isPullback_of_isPullbackVia {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
    {E : FakeEllipticCurve Λ N S} {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g) : IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨hg, -⟩ := h
  exact hg

theorem exists_point_Ab_of_coords {r : ℕ} {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'']
    [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'']
    (hcompat : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
      (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ))
    (s : Fin 2 → B'') :
    ∃ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
      PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) ∧
      PA ≫ ρ.gA = (θ₀ B'' s).1 := by
  obtain ⟨hsq, -⟩ := ρ.isPullback_Ab
  have hw : (θ₀ B'' s).1 ≫ A₀.f =
      Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) ≫
        Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) := by
    rw [(θ₀ B'' s).2]
    change Spec.map (CommRingCat.ofHom (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'')) = _
    rw [hcompat, CommRingCat.ofHom_comp, Spec.map_comp]
  exact ⟨hsq.lift _ _ hw, hsq.lift_snd _ _ hw, hsq.lift_fst _ _ hw⟩

end SLinAux

theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (n : ℕ) :
    (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n)).comp σ =
      σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries n)) := by
  classical
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnΛ : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by simpa using hΛℤ n

  have hN0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n) i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (X.F.nthSeries n i)) = 0
    rw [MvPowerSeries.constantCoeff_map, MvFormalGroup.constantCoeff_nthSeries, map_zero]
  have hN0' : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries n) i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (X₀.F.nthSeries n i)) = 0
    rw [MvPowerSeries.constantCoeff_map, MvFormalGroup.constantCoeff_nthSeries, map_zero]
  apply GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
    E.L X.F θ hE.1 (Ideal.span {algebraMap 𝒪 B π}) _ _ (fun i => Series.constantCoeff_comp hN0 hσ0 i) (fun i => Series.constantCoeff_comp hσ0 hN0' i)
  intro B'' _ _ _ hc J m hJ s hs

  letI : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' :=
    ((algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
  have hc2 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
      (algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := rfl

  set t : Fin 2 → B'' := fun j => MvFormalGroup.nilEval m (σ j) s with ht
  set s₁ : Fin 2 → B'' := fun l => MvFormalGroup.nilEval m (X₀.F.nthSeries n l) s with hs₁
  have htJ : ∀ j, t j ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσ0 (0 : MvPowerSeries (Fin 2) _)).1 j
  have hs₁J : ∀ l, s₁ l ∈ J := fun l =>
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs (X₀.F.nthSeries n) (fun i => MvFormalGroup.constantCoeff_nthSeries _ _ i) (0 : MvPowerSeries (Fin 2) _)).1 l

  have hL : (fun i => MvFormalGroup.nilEval m ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n)).comp σ i) s) =
      fun i => MvFormalGroup.nilEval m (((n : ℕ) : MvFormalGroup.End X.F).toPowerSeries i) t := by
    funext i
    show MvFormalGroup.nilEval m (MvPowerSeries.subst σ (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n i))) s = _
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσ0 _).2,
      SLinAux.nilEval_map_of_algebraMap_eq (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hc, MvFormalGroup.End.toPowerSeries_natCast]
  have hR : (fun i => MvFormalGroup.nilEval m ((σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries n))) i) s) =
      fun i => MvFormalGroup.nilEval m (σ i) s₁ := by
    funext i
    show MvFormalGroup.nilEval m (MvPowerSeries.subst (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries n)) (σ i)) s = _
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hN0' _).2]
    congr 1
    funext l
    show MvFormalGroup.nilEval m (MvPowerSeries.map _ (X₀.F.nthSeries n l)) s = _
    rw [SLinAux.nilEval_map_of_algebraMap_eq (FakeEllipticCurve.Rigidification.residueLeg π ψ) hc2]
  rw [hL, hR,
    CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia E coord hcoord X θ hE h1Λ n (hnΛ _)
      B'' J m hJ t htJ]

  obtain ⟨PA, hPAf, hPAg⟩ := SLinAux.exists_point_Ab_of_coords π ρ θ₀ B'' hc2 s
  have hact_gb : ∀ x : ↥Λ, ρ.Eb.act x ≫ ρ.gb = ρ.gb ≫ E.act x := SLinAux.act_comp_of_isPullbackVia ρ.isPullback_Eb
  have hact_gA : ∀ x : ↥Λ, ρ.Ab.act x ≫ ρ.gA = ρ.gA ≫ A₀.act x := SLinAux.act_comp_of_isPullbackVia ρ.isPullback_Ab
  obtain ⟨-, -, -, -, -, hφ'Λ, -⟩ := ρ.isIsogenyPair

  have hP1f : (PA ≫ ρ.Ab.act ⟨((n : ℕ) : ℚ), hnΛ n⟩) ≫ ρ.Ab.f =
      Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'')) := by
    rw [Category.assoc, ρ.Ab.act_over, hPAf]
  have hP1g : (PA ≫ ρ.Ab.act ⟨((n : ℕ) : ℚ), hnΛ n⟩) ≫ ρ.gA = (θ₀ B'' s₁).1 := by
    have hINT0 := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia A₀ coord hcoord X₀ θ₀ hA₀ h1Λ n (hnΛ _)
        B'' J m hJ s hs
    rw [MvFormalGroup.End.toPowerSeries_natCast] at hINT0
    rw [Category.assoc, hact_gA, ← Category.assoc, hPAg, hs₁, hINT0, mapPt_coe]
  have h2 := hσ B'' hc hc2 J m hJ s₁ hs₁J _ hP1f hP1g
  have h1 := hσ B'' hc hc2 J m hJ s hs PA hPAf hPAg

  have key : (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s₁)).1 = (θ B'' t).1 ≫ E.act ⟨((n : ℕ) : ℚ), hnΛ n⟩ := by
    rw [← h2, ← h1]
    simp only [Category.assoc]
    rw [← hact_gb, ← Category.assoc (ρ.Ab.act _) ρ.φ', hφ'Λ, Category.assoc]
  apply Subtype.ext
  rw [mapPt_coe, ← key]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval (solution)

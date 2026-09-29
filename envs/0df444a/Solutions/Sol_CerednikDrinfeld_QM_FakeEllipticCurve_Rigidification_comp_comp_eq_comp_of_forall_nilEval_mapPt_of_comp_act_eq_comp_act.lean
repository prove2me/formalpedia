-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_comp_eq_comp_of_forall_nilEval_mapPt_of_comp_act_eq_comp_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c7036fa3-b057-549d-a452-d75cdd920a5d

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_comp_eq_comp_of_forall_nilEval_mapPt_of_comp_act_eq_comp_act

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace T2aAux

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

end T2aAux

theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (E Ef : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f)
    (hEf : Ef.IsFormalModuleVia coord X (fun B' _ _ s => mapPt q hq (θ B' s)))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

    (σ σf : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσf0 : ∀ i, MvPowerSeries.constantCoeff (σf i) = 0)
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
    (hσf : (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρf.Ab.A,
            PA ≫ ρf.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρf.gA = (θ₀ B'' s).1 →
              PA ≫ ρf.φ' ≫ ρf.gb = (mapPt q hq (θ B'' (fun i => MvFormalGroup.nilEval m (σf i) s))).1))

    (qb : ρ.Eb.A ⟶ ρf.Eb.A) (hqb : qb ≫ ρf.gb = ρ.gb ≫ q)
    (uA : ρf.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (huAg : uA ≫ ρ.gA = ρf.gA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (n n' : ℕ)
    (hcurve : uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρf.φ' ≫ ρf.Eb.act ⟨(((n' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s)) :
    (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n)).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries)) =
      (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n')).comp σf := by
  classical

  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnΛ : ∀ k : ℕ, ((k : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun k => by simpa using hΛℤ k
  have hΛeq : ∀ k : ℕ, (⟨((k : ℕ) : ℚ), hnΛ k⟩ : ↥Λ) = ⟨(((k : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := fun k => Subtype.ext (by push_cast; rfl)

  have hN0 : ∀ (k : ℕ) (i : Fin 2), MvPowerSeries.constantCoeff (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries k) i) = 0 := by
    intro k i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (X.F.nthSeries k i)) = 0
    rw [MvPowerSeries.constantCoeff_map, MvFormalGroup.constantCoeff_nthSeries, map_zero]
  have hε0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (ε'.toPowerSeries i)) = 0
    rw [MvPowerSeries.constantCoeff_map, ε'.constantCoeff_eq_zero, map_zero]
  have hσε0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      ((σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries)) i) = 0 :=
    fun i => Series.constantCoeff_comp hσ0 hε0 i
  apply GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
    Ef.L X.F (fun B' _ _ s => mapPt q hq (θ B' s)) hEf.1 (Ideal.span {algebraMap 𝒪 B π}) _ _
    (fun i => Series.constantCoeff_comp (hN0 _) hσε0 i) (fun i => Series.constantCoeff_comp (hN0 _) hσf0 i)
  intro B'' _ _ _ hc J m hJ s hs

  letI : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' :=
    ((algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
  have hc2 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
      (algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := rfl

  set tf : Fin 2 → B'' := fun j => MvFormalGroup.nilEval m (σf j) s with htf
  set s₁ : Fin 2 → B'' := fun l => MvFormalGroup.nilEval m (ε'.toPowerSeries l) s with hs₁
  set t₂ : Fin 2 → B'' := fun j => MvFormalGroup.nilEval m (σ j) s₁ with ht₂
  have htfJ : ∀ j, tf j ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σf hσf0 (0 : MvPowerSeries (Fin 2) _)).1 j
  have hs₁J : ∀ l, s₁ l ∈ J := fun l =>
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs ε'.toPowerSeries ε'.constantCoeff_eq_zero (0 : MvPowerSeries (Fin 2) _)).1 l
  have ht₂J : ∀ j, t₂ j ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J m hJ s₁ hs₁J σ hσ0 (0 : MvPowerSeries (Fin 2) _)).1 j

  have hL : (fun i => MvFormalGroup.nilEval m ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n)).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries)) i) s) =
      fun i => MvFormalGroup.nilEval m (((n : ℕ) : MvFormalGroup.End X.F).toPowerSeries i) t₂ := by
    funext i
    show MvFormalGroup.nilEval m (MvPowerSeries.subst (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries))
      (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n i))) s = _
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hσε0 _).2,
      T2aAux.nilEval_map_of_algebraMap_eq (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hc, MvFormalGroup.End.toPowerSeries_natCast]
    congr 1
    funext j
    show MvFormalGroup.nilEval m (MvPowerSeries.subst (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries) (σ j)) s = _
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hε0 _).2]
    congr 1
    funext l
    exact T2aAux.nilEval_map_of_algebraMap_eq (FakeEllipticCurve.Rigidification.residueLeg π ψ) hc2 m (ε'.toPowerSeries l) s
  have hR : (fun i => MvFormalGroup.nilEval m ((Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n')).comp σf i) s) =
      fun i => MvFormalGroup.nilEval m (((n' : ℕ) : MvFormalGroup.End X.F).toPowerSeries i) tf := by
    funext i
    show MvFormalGroup.nilEval m (MvPowerSeries.subst σf (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries n' i))) s = _
    rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σf hσf0 _).2,
      T2aAux.nilEval_map_of_algebraMap_eq (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) hc, MvFormalGroup.End.toPowerSeries_natCast]
  rw [hL, hR]
  have h342a := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia Ef coord hcoord X
    (fun B' _ _ s => mapPt q hq (θ B' s)) hEf h1Λ n (hnΛ _) B'' J m hJ t₂ ht₂J
  have h342b := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia Ef coord hcoord X
    (fun B' _ _ s => mapPt q hq (θ B' s)) hEf h1Λ n' (hnΛ _) B'' J m hJ tf htfJ
  rw [h342a, h342b]

  obtain ⟨P', hP'f, hP'A⟩ := T2aAux.exists_point_Ab_of_coords π ρf θ₀ B'' hc2 s
  have hact_gb : ∀ x : ↥Λ, ρ.Eb.act x ≫ ρ.gb = ρ.gb ≫ E.act x := T2aAux.act_comp_of_isPullbackVia ρ.isPullback_Eb
  have hact_gbf : ∀ x : ↥Λ, ρf.Eb.act x ≫ ρf.gb = ρf.gb ≫ Ef.act x := T2aAux.act_comp_of_isPullbackVia ρf.isPullback_Eb

  have hright : P' ≫ (ρf.φ' ≫ ρf.Eb.act ⟨(((n' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρf.gb =
      (mapPt q hq (θ B'' tf)).1 ≫ Ef.act ⟨(((n' : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [← hσf B'' hc hc2 J m hJ s hs P' hP'f hP'A]
    simp only [Category.assoc]
    rw [hact_gbf]

  have hsq_uA := T2aAux.isPullback_of_isPullbackVia huA
  have hPf : (P' ≫ uA ≫ f'b) ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ (Ideal.span {algebraMap 𝒪 B π})) B'')) := by
    simp only [Category.assoc]
    rw [hf'bf, hsq_uA.w, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, hP'f]
  have hPA : (P' ≫ uA ≫ f'b) ≫ ρ.gA = (θ₀ B'' s₁).1 := by
    simp only [Category.assoc]
    rw [hf'b, ← Category.assoc uA ρ.gA, huAg, ← Category.assoc, hP'A, hs₁, hε' B'' J m hJ s hs, mapPt_coe]

  have hleft : P' ≫ (uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩) ≫ ρf.gb =
      (mapPt q hq (θ B'' t₂)).1 ≫ Ef.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by
    rw [mapPt_coe, ← hσ B'' hc hc2 J m hJ s₁ hs₁J (P' ≫ uA ≫ f'b) hPf hPA]
    simp only [Category.assoc]
    rw [hact_gbf, ← Category.assoc qb ρf.gb, hqb, Category.assoc]
  have key := congrArg (fun φ => P' ≫ φ ≫ ρf.gb) hcurve
  rw [hleft, hright] at key
  apply Subtype.ext
  rw [mapPt_coe, mapPt_coe, hΛeq, hΛeq]
  exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_comp_eq_comp_of_forall_nilEval_mapPt_of_comp_act_eq_comp_act
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_comp_eq_comp_of_forall_nilEval_mapPt_of_comp_act_eq_comp_act (solution)

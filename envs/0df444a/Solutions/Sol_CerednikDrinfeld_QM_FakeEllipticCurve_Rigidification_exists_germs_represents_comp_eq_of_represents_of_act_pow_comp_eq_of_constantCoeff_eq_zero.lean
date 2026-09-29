-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e37d6d77-26fe-524a-8be1-5f2a6945d933

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem solution
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (hkr : IsNilpotent ((r : ℕ) : k))
    (ψ : Onr →ₐ[𝒪] k)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ k ψ)
    (X X' : FormalODModule r k)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (T₀ : FormalODModule.Hom X X')

    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (θA : RelativeGroupLaw.FormalCoordinates x.2.Ab.f 2)
    (hθA : x.2.Ab.IsFormalModuleVia coord (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA)
    (hθAg : ∀ (B'' : Type) [CommRing B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''],
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
      ∀ (s : Fin 2 → B''), (∀ i, IsNilpotent (s i)) → (θA B'' s).1 ≫ x.2.gA = (θ₀ B'' s).1)

    (θE : RelativeGroupLaw.FormalCoordinates x.2.Eb.f 2) (θE' : RelativeGroupLaw.FormalCoordinates x'.2.Eb.f 2)
    (hθE : x.2.Eb.IsFormalModuleVia coord (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE)
    (hθE' : x'.2.Eb.IsFormalModuleVia coord (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))) θE')
    (hθEg : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE B'' s).1 ≫ x.2.gb = (θ B'' s).1)
    (hθEg' : ∀ (B'' : Type) [CommRing B''] [Algebra k B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'']
      [IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (s : Fin 2 → B''),
      (∀ i, IsNilpotent (s i)) → (θE' B'' s).1 ≫ x'.2.gb = (θ' B'' s).1)

    (v : x.2.Ab.A ⟶ x'.2.Ab.A) (hv : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x'.2.Ab x.2.Ab v) (hvg : v ≫ x'.2.gA = x.2.gA)

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (κB : (k ⧸ Ideal.span {algebraMap 𝒪 k π}) →+* (k ⧸ pIdeal r k))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 k π})) = Ideal.Quotient.mk (pIdeal r k))
    (hκB' : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* k)).comp κ)
    (σ σ' : Series (k ⧸ Ideal.span {algebraMap 𝒪 k π}))
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (hσ : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x.2.Ab.A,
            PA ≫ x.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x.2.gA = (θ₀ B'' s).1 →
              PA ≫ x.2.φ' ≫ x.2.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1))
    (hσ' : (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] [Algebra k B''] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap k B'' = (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ x'.2.Ab.A,
            PA ≫ x'.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) →
            PA ≫ x'.2.gA = (θ₀ B'' s).1 →
              PA ≫ x'.2.φ' ≫ x'.2.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1))
    (c₀ c c' : ℕ)
    (heq : (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c)).comp
          ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r k))).comp (σ.map κB))).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀)) =
      (((X'.map (Ideal.Quotient.mk (pIdeal r k))).act ((r : Zp2 r) ^ c')).comp (σ'.map κB)).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* k))).act ((r : Zp2 r) ^ c₀))) :
    ∃ σ₁ σ₁' : Series (k ⧸ Ideal.span {algebraMap 𝒪 k π}),
      (∀ i, MvPowerSeries.constantCoeff (σ₁ i) = 0) ∧ (∀ i, MvPowerSeries.constantCoeff (σ₁' i) = 0) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ x.2.φ' ≫ x.2.Eb.act ⟨(((r ^ c : ℕ) : ℤ) : ℚ), hΛℤ _⟩) =
            (θE B'' (fun i => MvFormalGroup.nilEval n (σ₁ i) s)).1) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θA B'' s).1 ≫ (x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ v ≫ x'.2.φ' ≫ x'.2.Eb.act ⟨(((r ^ c' : ℕ) : ℤ) : ℚ), hΛℤ _⟩) =
            (θE' B'' (fun i => MvFormalGroup.nilEval n (σ₁' i) s)).1) ∧
      (T₀.toSeries.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).comp σ₁ = σ₁' := by
  classical

  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnc₀ : (((r ^ c₀ : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ c₀ : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hnc : (((r ^ c : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ c : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hnc' : (((r ^ c' : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ c' : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have ez : ∀ (e : ℕ) (he : (((r ^ e : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ),
      (⟨(((r ^ e : ℕ) : ℤ) : ℚ), hΛℤ _⟩ : ↥Λ) = ⟨((r ^ e : ℕ) : ℚ), he⟩ := fun e he =>
    Subtype.ext (by push_cast; rfl)

  have hAc : (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) =
      MvFormalGroup.Hom.toPowerSeries ((r ^ c₀ : ℕ) : MvFormalGroup.End (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).F) := by
    rw [← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]
  have hRc : (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c) =
      MvFormalGroup.Hom.toPowerSeries ((r ^ c : ℕ) : MvFormalGroup.End (X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).F) := by
    rw [← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]
  have hRc' : (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c') =
      MvFormalGroup.Hom.toPowerSeries ((r ^ c' : ℕ) : MvFormalGroup.End (X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).F) := by
    rw [← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]
  have cA : ∀ i, MvPowerSeries.constantCoeff ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) i) = 0 :=
    ((X₀.map _).isLawHom_act _).1
  have cR : ∀ i, MvPowerSeries.constantCoeff ((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c) i) = 0 :=
    ((X.map _).isLawHom_act _).1
  have cR' : ∀ i, MvPowerSeries.constantCoeff ((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c') i) = 0 :=
    ((X'.map _).isLawHom_act _).1
  have cσA := Series.constantCoeff_comp hσ0 cA
  have cσ'A := Series.constantCoeff_comp hσ'0 cA

  obtain ⟨hsqE, -, -, -⟩ := x.2.isPullback_Eb
  obtain ⟨hsqE', -, -, -⟩ := x'.2.isPullback_Eb
  obtain ⟨-, hφ'f, -⟩ := x.2.isIsogenyPair
  obtain ⟨-, hφ'f', -⟩ := x'.2.isIsogenyPair
  obtain ⟨hsqv, -, -, -⟩ := id hv
  refine ⟨((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c)).comp
      (σ.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀))),
    ((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c')).comp
      (σ'.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀))),
    Series.constantCoeff_comp cR cσA, Series.constantCoeff_comp cR' cσ'A, ?_, ?_, ?_⟩
  ·
    intro B'' _ _ J n hJ s hs
    letI algk : Algebra k B'' := ((algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).toAlgebra
    haveI : IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI algO : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' :=
      ((algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    have hnil : ∀ (u : Fin 2 → B''), (∀ i, u i ∈ J) → ∀ i, IsNilpotent (u i) := fun u hu i =>
      ⟨n + 1, by have h := Ideal.pow_mem_pow (hu i) (n + 1); rw [hJ] at h; exact (Submodule.mem_bot _).mp h⟩

    have hsA := (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cA (0 : MvPowerSeries (Fin 2) _)).1
    have eA : (θA B'' s).1 ≫ x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        (θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 := by
      have h := congrArg Subtype.val
        (CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
          x.2.Ab coord hcoord _ θA hθA h1Λ (r ^ c₀) hnc₀ B'' J n hJ s hs)
      rw [mapPt_coe] at h
      rw [ez c₀ hnc₀, ← h, hAc]

    have eB := hσ B'' rfl rfl J n hJ _ hsA (θA B'' _).1 (θA B'' _).2 (hθAg B'' rfl _ (hnil _ hsA))

    have hsE := (MvFormalGroup.nilEval_subst_of_mem J n hJ _ hsA σ hσ0 (0 : MvPowerSeries (Fin 2) _)).1
    have eC : (θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 ≫ x.2.φ' =
        (θE B'' (fun i => MvFormalGroup.nilEval n (σ i) (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s))).1 := by
      apply hsqE.hom_ext
      · rw [Category.assoc, eB]
        exact (hθEg B'' _ (hnil _ hsE)).symm
      · rw [Category.assoc, hφ'f, (θA B'' _).2]
        exact (θE B'' _).2.symm

    have eD := congrArg Subtype.val
      (CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
        x.2.Eb coord hcoord _ θE hθE h1Λ (r ^ c) hnc B'' J n hJ _ hsE)
    rw [mapPt_coe, ← hRc, ← ez c hnc] at eD

    rw [← Category.assoc, ← Category.assoc, eA, eC, ← eD]
    congr 2
    funext i
    rw [show (((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c)).comp
        (σ.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))) i =
        MvPowerSeries.subst (σ.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))
          ((X.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c) i) from rfl,
      (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cσA _).2]
    congr 1
    funext j
    exact (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cA (σ j)).2.symm
  ·
    intro B'' _ _ J n hJ s hs
    letI algk : Algebra k B'' := ((algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).toAlgebra
    haveI : IsScalarTower k (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI algO : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' :=
      ((algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    have hnil : ∀ (u : Fin 2 → B''), (∀ i, u i ∈ J) → ∀ i, IsNilpotent (u i) := fun u hu i =>
      ⟨n + 1, by have h := Ideal.pow_mem_pow (hu i) (n + 1); rw [hJ] at h; exact (Submodule.mem_bot _).mp h⟩
    have hsA := (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cA (0 : MvPowerSeries (Fin 2) _)).1
    have eA : (θA B'' s).1 ≫ x.2.Ab.act ⟨(((r ^ c₀ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
        (θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 := by
      have h := congrArg Subtype.val
        (CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
          x.2.Ab coord hcoord _ θA hθA h1Λ (r ^ c₀) hnc₀ B'' J n hJ s hs)
      rw [mapPt_coe] at h
      rw [ez c₀ hnc₀, ← h, hAc]

    have hPf : ((θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 ≫ v) ≫ x'.2.Ab.f =
        Spec.map (CommRingCat.ofHom (algebraMap (k ⧸ Ideal.span {algebraMap 𝒪 k π}) B'')) := by
      rw [Category.assoc, hsqv.w, ← Category.assoc, (θA B'' _).2]
      simp
    have hPg : ((θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 ≫ v) ≫ x'.2.gA =
        (θ₀ B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 := by
      rw [Category.assoc, hvg]
      exact hθAg B'' rfl _ (hnil _ hsA)
    have eB := hσ' B'' rfl rfl J n hJ _ hsA _ hPf hPg
    have hsE := (MvFormalGroup.nilEval_subst_of_mem J n hJ _ hsA σ' hσ'0 (0 : MvPowerSeries (Fin 2) _)).1
    have eC : ((θA B'' (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s)).1 ≫ v) ≫ x'.2.φ' =
        (θE' B'' (fun i => MvFormalGroup.nilEval n (σ' i) (fun j => MvFormalGroup.nilEval n
          ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀) j) s))).1 := by
      apply hsqE'.hom_ext
      · rw [Category.assoc, eB]
        exact (hθEg' B'' _ (hnil _ hsE)).symm
      · rw [Category.assoc, hφ'f', hPf]
        exact (θE' B'' _).2.symm
    have eD := congrArg Subtype.val
      (CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
        x'.2.Eb coord hcoord _ θE' hθE' h1Λ (r ^ c') hnc' B'' J n hJ _ hsE)
    rw [mapPt_coe, ← hRc', ← ez c' hnc'] at eD
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, eA, eC, ← eD]
    congr 2
    funext i
    rw [show (((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c')).comp
        (σ'.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))) i =
        MvPowerSeries.subst (σ'.comp ((X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ c₀)))
          ((X'.map (algebraMap k (k ⧸ Ideal.span {algebraMap 𝒪 k π}))).act ((r : Zp2 r) ^ c') i) from rfl,
      (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cσ'A _).2]
    congr 1
    funext j
    exact (MvFormalGroup.nilEval_subst_of_mem J n hJ s hs _ cA (σ' j)).2.symm
  ·
    exact CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.map_hom_comp_germ_eq_germ_of_act_pow_comp_map_comp_act_pow_eq
      hrN 𝒪 π Onr Λ hΛ hΛℤ coord hcoord A₀ k hk hkr ψ x x' X X' θ θ' T₀ X₀ θ₀ hA₀ θA hθA hθAg θE θE' hθE hθE' hθEg hθEg'
      v hv hvg κ κB hκB hκB' σ σ' hσ0 hσ'0 hσ hσ' c₀ c c' heq

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_germs_represents_comp_eq_of_represents_of_act_pow_comp_eq_of_constantCoeff_eq_zero (solution)

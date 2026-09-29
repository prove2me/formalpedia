-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/41e492f1-cef8-5d33-a1c7-93d8a9a1afda

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace SandwichS25

theorem map_const {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (φ : Series R)
    (h : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Series.map f φ i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, h, map_zero]

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

theorem funext_same {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup 2 B) (θ : RelativeGroupLaw.FormalCoordinates f 2)
    (hθ : L.IsFormalCoordinates F θ) (σ σ' : Series B)
    (hσ : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ' : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (σ i) s) = θ B' (fun i => MvFormalGroup.nilEval m (σ' i) s)) :
    σ = σ' := by
  classical
  let e : B ⧸ (⊥ : Ideal B) ≃+* B := RingEquiv.quotientBot B
  have hmk : (e.symm.toRingHom : B →+* B ⧸ (⊥ : Ideal B)) = Ideal.Quotient.mk ⊥ := by
    ext x; exact RingEquiv.quotientBot_symm_mk x
  have key : σ.map e.symm.toRingHom = σ'.map e.symm.toRingHom := by
    apply RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero L F θ hθ ⊥
      _ _ (map_const _ σ hσ) (map_const _ σ' hσ')
    intro B' _ _ _ hc J m hJ s hs
    have hc' : algebraMap B B' = (algebraMap (B ⧸ (⊥ : Ideal B)) B').comp e.symm.toRingHom := by
      rw [hc, hmk]
    have e1 : (fun i => MvFormalGroup.nilEval m (Series.map e.symm.toRingHom σ i) s) =
        fun i => MvFormalGroup.nilEval m (σ i) s :=
      funext fun i => nilEval_map_of_algebraMap_eq _ hc' m (σ i) s
    have e2 : (fun i => MvFormalGroup.nilEval m (Series.map e.symm.toRingHom σ' i) s) =
        fun i => MvFormalGroup.nilEval m (σ' i) s :=
      funext fun i => nilEval_map_of_algebraMap_eq _ hc' m (σ' i) s
    rw [e1, e2]
    exact h B' J m hJ s hs
  have := congrArg (Series.map e.toRingHom) key
  rwa [Series.map_map, Series.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Series.map_ringHom_id,
    Series.map_ringHom_id] at this

theorem act_pow_eq {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (d : ℕ) :
    X.act ((p : Zp2 p) ^ d) = (((p ^ d : ℕ) : MvFormalGroup.End X.F)).toPowerSeries := by
  rw [← Nat.cast_pow]
  show (X.actRingHom ((p ^ d : ℕ) : Zp2 p)).toPowerSeries = _
  rw [map_natCast]

theorem isNilpotent_of_mem {B' : Type} [CommRing B'] {J : Ideal B'} {m : ℕ} (hJ : J ^ (m + 1) = ⊥) {x : B'} (hx : x ∈ J) :
    IsNilpotent x :=
  ⟨m + 1, by
    have := Ideal.pow_mem_pow hx (m + 1)
    rw [hJ] at this
    exact (Submodule.mem_bot _).mp this⟩

end SandwichS25

open SandwichS25 in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)

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

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (hX₀ : X₀.HasHeight 4)
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r Onr) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hBr : IsNilpotent ((r : ℕ) : B))
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)

    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hσ : FormalODModule.IsODHom (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ))
      (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ)
    (hrep : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
          (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) :
    ∃ τ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}),
      (∀ i, MvPowerSeries.constantCoeff (τ i) = 0) ∧
      FormalODModule.IsODHom (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})))
        (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) τ ∧
      τ.comp σ = (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).act ((r : Zp2 r) ^ ρ.d) ∧
      σ.comp τ = (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act ((r : Zp2 r) ^ ρ.d) := by
  classical

  letI algk : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
    (FakeEllipticCurve.Rigidification.residueLeg π ψ).toAlgebra
  have hBbr : IsNilpotent ((r : ℕ) : B ⧸ Ideal.span {algebraMap 𝒪 B π}) := by
    obtain ⟨m, hm⟩ := hBr
    exact ⟨m, by rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})), ← map_pow, hm, map_zero]⟩
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hmem : (((r ^ ρ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have h := hΛℤ ((r ^ ρ.d : ℕ) : ℤ)
    rwa [Int.cast_natCast] at h
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := hσ.constantCoeff

  obtain ⟨θb, hθb, hθbg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) E ρ.Eb ρ.gb ρ.isPullback_Eb X θ hX
  obtain ⟨θA, hθA, hθAg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) A₀ ρ.Ab ρ.gA ρ.isPullback_Ab X₀ θ₀ hA₀
  have hθb' : ρ.Eb.IsFormalModuleVia coord (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) θb := hθb
  have hθA' : ρ.Ab.IsFormalModuleVia coord (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA := hθA

  obtain ⟨hφo, hφ'o, hmul, hmul', hlin, hlin', hcomp⟩ := ρ.isIsogenyPair
  obtain ⟨hc1, hc2⟩ := hcomp hmem
  obtain ⟨τ, hτ, hτrep⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isODHom_forall_comp_eq_apply_nilEval_of_isFormalModuleVia coord hcoord hBbr
      ρ.Eb ρ.Ab ρ.φ hφo hmul hlin (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) θb hθb'
      (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) θA hθA'
  have hτ0 : ∀ i, MvPowerSeries.constantCoeff (τ i) = 0 := hτ.constantCoeff
  obtain ⟨hsqE, -⟩ := ρ.isPullback_Eb

  have step : ∀ (B' : Type) [CommRing B'] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'] [Algebra B B']
      [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'],
      algebraMap B B' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B').comp (Ideal.Quotient.mk _) →
      algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B' =
        (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
      ∀ (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ u : Fin 2 → B', (∀ i, u i ∈ J) →
        (θA B' u).1 ≫ ρ.φ' = (θb B' (fun i => MvFormalGroup.nilEval m (σ i) u)).1 := by
    intro B' _ _ _ _ hcB hck J m hJ u hu
    haveI : IsScalarTower B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B' :=
      IsScalarTower.of_algebraMap_eq (fun x => by rw [hcB]; rfl)
    haveI : IsScalarTower (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B' :=
      IsScalarTower.of_algebraMap_eq (fun x => by rw [hck]; rfl)
    have hσu : ∀ j, MvFormalGroup.nilEval m (σ j) u ∈ J := (MvFormalGroup.nilEval_subst_of_mem J m hJ u hu σ hσ0 0).1
    have hgA : (θA B' u).1 ≫ ρ.gA = (θ₀ B' u).1 := hθAg B' u (fun i => isNilpotent_of_mem hJ (hu i))
    have h1 := hrep B' hcB hck J m hJ u hu (θA B' u).1 (θA B' u).2 hgA
    apply hsqE.hom_ext
    · rw [Category.assoc, h1]
      exact (hθbg B' _ (fun i => isNilpotent_of_mem hJ (hσu i))).symm
    · rw [Category.assoc, hφ'o, (θA B' u).2, (θb B' _).2]
  refine ⟨τ, hτ0, hτ, ?_, ?_⟩
  ·
    rw [act_pow_eq]
    apply funext_same ρ.Ab.L (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)).F θA hθA'.1 _ _
      (Series.constantCoeff_comp hτ0 hσ0) (fun i => MvFormalGroup.Hom.constantCoeff_eq_zero _ i)
    intro B' _ _ J m hJ s hs
    letI : Algebra B B' := ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B').comp (Ideal.Quotient.mk _)).toAlgebra
    letI : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B' :=
      ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    have hσs : ∀ j, MvFormalGroup.nilEval m (σ j) s ∈ J := (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσ0 0).1
    have eL : (fun i => MvFormalGroup.nilEval m ((τ.comp σ) i) s) =
        fun i => MvFormalGroup.nilEval m (τ i) (fun j => MvFormalGroup.nilEval m (σ j) s) :=
      funext fun i => (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσ0 (τ i)).2
    rw [eL, CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia ρ.Ab coord hcoord
      _ θA hθA' h1Λ (r ^ ρ.d) hmem B' J m hJ s hs]
    apply Subtype.ext
    rw [mapPt_coe, ← hc2, ← Category.assoc, step B' rfl rfl J m hJ s hs,
      hτrep B' J m hJ _ hσs]
  ·
    rw [act_pow_eq]
    apply RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero E.L X.F θ hX.1
      (Ideal.span {algebraMap 𝒪 B π}) _ _ (Series.constantCoeff_comp hσ0 hτ0)
      (fun i => MvFormalGroup.Hom.constantCoeff_eq_zero _ i)
    intro B' _ _ _ hcB J m hJ s hs
    haveI : IsScalarTower B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B' :=
      IsScalarTower.of_algebraMap_eq (fun x => by rw [hcB]; rfl)
    letI : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B' :=
      ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    have hτs : ∀ j, MvFormalGroup.nilEval m (τ j) s ∈ J := (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs τ hτ0 0).1
    have hns : ∀ j, MvFormalGroup.nilEval m
        ((((r ^ ρ.d : ℕ) : MvFormalGroup.End (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).F)).toPowerSeries j) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ (fun i => MvFormalGroup.Hom.constantCoeff_eq_zero _ i) 0).1
    have eL : (fun i => MvFormalGroup.nilEval m ((σ.comp τ) i) s) =
        fun i => MvFormalGroup.nilEval m (σ i) (fun j => MvFormalGroup.nilEval m (τ j) s) :=
      funext fun i => (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs τ hτ0 (σ i)).2
    rw [eL]
    apply Subtype.ext
    rw [← hθbg B' _ (fun i => isNilpotent_of_mem hJ ((MvFormalGroup.nilEval_subst_of_mem J m hJ _ hτs σ hσ0 0).1 i)),
      ← hθbg B' _ (fun i => isNilpotent_of_mem hJ (hns i)),
      CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia ρ.Eb coord hcoord
        _ θb hθb' h1Λ (r ^ ρ.d) hmem B' J m hJ s hs,
      mapPt_coe, ← hc1, Category.assoc, Category.assoc, ← step B' hcB rfl J m hJ _ hτs, ← Category.assoc,
      hτrep B' J m hJ s hs, Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_comp_eq_act_pow_and_comp_eq_act_pow_of_isODHom_of_represents (solution)

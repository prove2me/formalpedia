-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/50055308-9b48-55c2-9dd1-434871a91621

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleVia_mapPt_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

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

    {n : ℕ} (P₀ : A₀.FullLevel n) (hrn : ¬ r ∣ n)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))

    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) (hiso : FakeEllipticCurve.IsoVia E E' i hi)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A) (hibg : ib ≫ ϱ'.gb = ϱ.gb ≫ i.hom) (hibf : ib ≫ ϱ'.Eb.f = ϱ.Eb.f)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA) (huAg : uA ≫ ϱ.gA = ϱ'.gA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (Pn : E.FullLevel n) (Pn' : E'.FullLevel n) (hPn : mapPt i.hom hi Pn.P = Pn'.P)
    (h : FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ Pn) :
    FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ϱ' Pn' := by
  obtain ⟨Q, hQf, hQg, X, θ, hXθ, j, t, hj, htX, htr, hadm, hlev⟩ := h

  have hXθ' := CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleVia.mapPt_of_iso coord B E E' i hi hiso.1 hiso.2.1 X θ hXθ
  obtain ⟨κB, σ, hκB, hκBψ, hσ, htρ⟩ := htr
  rcases subsingleton_or_nontrivial B with hBs | hBn
  ·
    haveI : IsEmpty (Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
    have hI := (isInitialOfIsEmpty (X := Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π}))))
    refine ⟨hI.to _, hI.hom_ext _ _, hI.hom_ext _ _, X, fun B'' _ _ s => mapPt i.hom hi (θ B'' s), hXθ', j, t, hj, htX,
      ⟨κB, σ, hκB, hκBψ, ?_, htρ⟩, hadm, hI.hom_ext _ _⟩
    intro B'' _ _ _ _ h1 h2 J m hJ s hs PA hPAf hPAg
    haveI : Subsingleton B'' := by
      refine subsingleton_of_zero_eq_one ?_
      have h01 : (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'') 1 = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'') 0 :=
        congrArg _ (Subsingleton.elim _ _)
      simpa using h01.symm
    haveI : IsEmpty (Spec (CommRingCat.of B'')) := inferInstanceAs (IsEmpty (PrimeSpectrum B''))
    exact (isInitialOfIsEmpty (X := Spec (CommRingCat.of B''))).hom_ext _ _

  obtain ⟨σ', hOD', hrep', hid'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr (by assumption) Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ P₀ hrn B ψ hB E E' i hi hiso ϱ ϱ' ib hibg hibf uA huA huAg i₁ j₁ hcorr Pn Pn' hPn Q hQf hQg X θ hXθ j t hj htX hadm hlev κB σ hκB hκBψ hσ htρ

  obtain ⟨n', hn', hiso'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr (by assumption) Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ P₀ hrn B ψ hB E E' i hi hiso ϱ ϱ' ib hibg hibf uA huA huAg i₁ j₁ hcorr Pn Pn' hPn Q hQf hQg X θ hXθ j t hj htX hadm hlev κB σ hκB hκBψ hσ htρ σ' hOD' hid'

  obtain ⟨Q', hQ'f, hQ'g, hlev'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_section_nsmulPt_pow_eq_of_corr_of_nsmulPt_pow_eq
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr (by assumption) Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ P₀ hrn B ψ hB E E' i hi hiso ϱ ϱ' ib hibg hibf uA huA huAg i₁ j₁ hcorr Pn Pn' hPn Q hQf hQg X θ hXθ j t hj htX hadm hlev κB σ hκB hκBψ hσ htρ n' hn'
  refine ⟨Q', hQ'f, hQ'g, X, fun B'' _ _ s => mapPt i.hom hi (θ B'' s), hXθ', j,
    { X := X, n := n',
      ρ := (Series.map κB σ').comp
        ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
          (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) },
    hj, rfl, ⟨κB, σ', hκB, hκBψ, hrep', rfl⟩, ?_, hlev'⟩

  obtain ⟨hsp, hh4, -⟩ := hadm
  rw [htX] at hsp hh4
  exact ⟨hsp, hh4, hiso'⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isNormLevelTransport_of_isoVia_of_corr_of_isFormalModuleVia (solution)

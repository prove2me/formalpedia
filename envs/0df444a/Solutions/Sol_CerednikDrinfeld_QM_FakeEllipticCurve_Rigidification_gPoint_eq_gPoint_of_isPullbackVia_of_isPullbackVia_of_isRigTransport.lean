-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.gPoint_eq_gPoint_of_isPullbackVia_of_isPullbackVia_of_isRigTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1a38e82a-1334-5e3c-8488-2895ccc4fc94

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isoVia_corr_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eta_eq_of_isoVia_of_corr_of_isRigTransport
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_eq_of_forall_map_eq_of_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_gPoint_eq_gPoint_of_isPullbackVia_of_isPullbackVia_of_isRigTransport
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

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

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra 𝒪 L] (hL : IsNilpotent (algebraMap 𝒪 L π)) (hLr : IsNilpotent ((r : ℕ) : L))
    (φ₁ φ₂ : B →ₐ[𝒪] L) (hφ : φ₁ = φ₂)

    (x₁ : FakeEllipticCurve.RigidifiedCurve r π A₀ L (φ₁.comp ψ)) (g₁ : x₁.1.A ⟶ x.1.A)
    (hg₁ : FakeEllipticCurve.IsPullbackVia (φ₁ : B →+* L) x.1 x₁.1 g₁)
    (hρ₁ : FakeEllipticCurve.Rigidification.IsPullbackVia φ₁ g₁ hg₁ x.2 x₁.2)
    (X₁ : FormalODModule r L) (θ₁ : RelativeGroupLaw.FormalCoordinates x₁.1.f 2) (hX₁ : x₁.1.IsFormalModuleVia coord X₁ θ₁)
    (j₁ : ℕ) (t₁ : Rigidified r Φ L) (hj₁ : j₁ ≤ 1) (ht₁X : t₁.X = X₁)
    (htr₁ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x₁.2 θ₁ j₁ t₁)
    (hadm₁ : t₁.IsAdmissible ι ((frobTwist Onr Fr (-(j₁ : ℤ)) (φ₁.comp ψ) : Onr →ₐ[𝒪] L) : Onr →+* L))

    (x₂ : FakeEllipticCurve.RigidifiedCurve r π A₀ L (φ₂.comp ψ)) (g₂ : x₂.1.A ⟶ x.1.A)
    (hg₂ : FakeEllipticCurve.IsPullbackVia (φ₂ : B →+* L) x.1 x₂.1 g₂)
    (hρ₂ : FakeEllipticCurve.Rigidification.IsPullbackVia φ₂ g₂ hg₂ x.2 x₂.2)
    (X₂ : FormalODModule r L) (θ₂ : RelativeGroupLaw.FormalCoordinates x₂.1.f 2) (hX₂ : x₂.1.IsFormalModuleVia coord X₂ θ₂)
    (j₂ : ℕ) (t₂ : Rigidified r Φ L) (hj₂ : j₂ ≤ 1) (ht₂X : t₂.X = X₂)
    (htr₂ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x₂.2 θ₂ j₂ t₂)
    (hadm₂ : t₂.IsAdmissible ι ((frobTwist Onr Fr (-(j₂ : ℤ)) (φ₂.comp ψ) : Onr →ₐ[𝒪] L) : Onr →+* L))
    :
    (⟨frobTwist Onr Fr (-(j₁ : ℤ)) (φ₁.comp ψ), hLr,
        η L ((frobTwist Onr Fr (-(j₁ : ℤ)) (φ₁.comp ψ) : Onr →ₐ[𝒪] L) : Onr →+* L) hLr t₁⟩ : ModuliPackage.GPoint 𝒪 M L) =
      ⟨frobTwist Onr Fr (-(j₂ : ℤ)) (φ₂.comp ψ), hLr,
        η L ((frobTwist Onr Fr (-(j₂ : ℤ)) (φ₂.comp ψ) : Onr →ₐ[𝒪] L) : Onr →+* L) hLr t₂⟩ := by
  classical
  subst hφ

  have hid : (Iso.refl x.1.A).hom ≫ x.1.f = x.1.f := Category.id_comp _
  have hmp : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t x.1.f),
      mapPt (Iso.refl x.1.A).hom hid P = P := fun t P => Subtype.ext (Category.comp_id _)
  have hiso : FakeEllipticCurve.IsoVia x.1 x.1 (Iso.refl x.1.A) hid := by
    refine ⟨fun t P Q => ?_, fun m => ?_, fun t P => ?_⟩
    · rw [hmp, hmp, hmp]
    · simp
    · rw [hmp]
  have hibg : 𝟙 x.2.Eb.A ≫ x.2.gb = x.2.gb ≫ (Iso.refl x.1.A).hom := by simp
  have hibf : 𝟙 x.2.Eb.A ≫ x.2.Eb.f = x.2.Eb.f := Category.id_comp _
  have huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x.2.Ab (𝟙 x.2.Ab.A) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id _ x.2.Ab
  have huAg : 𝟙 x.2.Ab.A ≫ x.2.gA = x.2.gA := Category.id_comp _
  have hcorr : 𝟙 x.2.Eb.A ≫ x.2.φ ≫ 𝟙 x.2.Ab.A ≫ x.2.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      x.2.φ ≫ x.2.Ab.act ⟨(((r ^ 0 : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by simp

  obtain ⟨iφ, hiφ, hisoφ, -, ibφ, hibφg, hibφf, uAφ, huAφ, huAφg, hcorrφ⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isoVia_corr_of_isPullbackVia
      𝒪 π Onr Λ hΛℤ A₀ B L φ₁ ψ x.1 x.1 (Iso.refl x.1.A) hid hiso x.2 x.2 (𝟙 _) hibg hibf (𝟙 _) huA huAg 0 0 hcorr
      x₁.1 g₁ hg₁ x₂.1 g₂ hg₂ x₁.2 hρ₁ x₂.2 hρ₂

  rcases subsingleton_or_nontrivial L with hLs | hLn
  ·
    have hf0 : Ideal.span (Set.range (Fin.elim0 : Fin 0 → L)) = (⊤ : Ideal L) := by
      haveI : Subsingleton (Ideal L) := (Submodule.subsingleton_iff L).mpr hLs
      exact Subsingleton.elim _ _
    haveI hAw : ∀ i : Fin 0, IsLocalization.Away ((Fin.elim0 : Fin 0 → L) i) L := fun i => i.elim0
    exact CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.eq_of_forall_map_eq_of_span_eq_top
      hM L 0 Fin.elim0 hf0 (fun _ => L) _ _ (fun i => i.elim0)
  ·
    obtain ⟨hj, -, hη12⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eta_eq_of_isoVia_of_corr_of_isRigTransport
        hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr
      ‹IsIndefiniteRamifiedExactlyAt a b r rbar› Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀
      κ hκ n₀ β₀ hβ₀
        L (φ₁.comp ψ) hL hLr x₁.1 x₂.1 iφ hiφ hisoφ x₁.2 x₂.2 ibφ hibφg hibφf uAφ huAφ huAφg 0 0 hcorrφ
        X₁ θ₁ hX₁ j₁ t₁ hj₁ ht₁X htr₁ hadm₁ X₂ θ₂ hX₂ j₂ t₂ hj₂ ht₂X htr₂ hadm₂
    subst hj
    rw [hη12]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_gPoint_eq_gPoint_of_isPullbackVia_of_isPullbackVia_of_isRigTransport
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_gPoint_eq_gPoint_of_isPullbackVia_of_isPullbackVia_of_isRigTransport (solution)

-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.n_eq_n_add_of_isRigTransport_of_isRigTransport_frobTwist_neg_one_of_isActBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2e8157eb-c1a8-5ae1-a500-b4f424f0a151

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_succ_of_isRigTransport_frobTwist_neg_one
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_eq_and_n_eq_and_eta_eq_of_isRigTransport_of_isRigTransport
import Theorems.Thm_CerednikDrinfeld_FormalOmega_eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_parity_mod_two_eq_of_isRigTransport_of_isAdmissible
import Theorems.Thm_CerednikDrinfeld_FormalODModule_two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_n_eq_n_add_of_isRigTransport_of_isRigTransport_frobTwist_neg_one_of_isActBy
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

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 M B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (A₀r : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (prA : A₀r.A ⟶ A₀.A)
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr.symm : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
    (F : A₀.A ⟶ A₀r.A) (hF : F ≫ A₀r.f = A₀.f) (V : A₀r.A ⟶ A₀.A) (hV : V ≫ A₀.f = A₀r.f)
    (F_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
      mapPt F hF (A₀.L.mul t P Q) = A₀r.L.mul t (mapPt F hF P) (mapPt F hF Q))
    (V_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀r.f),
      mapPt V hV (A₀r.L.mul t P Q) = A₀.L.mul t (mapPt V hV P) (mapPt V hV Q))
    (F_act : ∀ x : ↥Λ, A₀.act x ≫ F = F ≫ A₀r.act x) (V_act : ∀ x : ↥Λ, A₀r.act x ≫ V = V ≫ A₀.act x)
    (F_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      FactorsThrough A₀.lev P → FactorsThrough A₀r.lev (mapPt F hF P))
    (V_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      FactorsThrough A₀r.lev Q → FactorsThrough A₀.lev (mapPt V hV Q))
    (V_F : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P : SchemeHomOver t A₀.f),
      mapPt V hV (mapPt F hF P) = nsmulPt A₀.L t r P)
    (F_V : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (Q : SchemeHomOver t A₀r.f),
      mapPt F hF (mapPt V hV Q) = nsmulPt A₀r.L t r Q)
    (V_frob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀r.A),
      x ≫ V = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x ≫ prA)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (-1) ψ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)
    (hd : ρp.d = ρ.d + 1) (hφ : ub ≫ ρp.φ = ρ.φ ≫ Fb) (hφ' : ρp.φ' = Vb ≫ ρ.φ' ≫ ub)

    (hBr : IsNilpotent ((r : ℕ) : B))
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (X' : FormalODModule r B) (θ' : RelativeGroupLaw.FormalCoordinates E.f 2) (hX' : E.IsFormalModuleVia coord X' θ')
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X')
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρp θ' j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr (-1) ψ) : Onr →ₐ[𝒪] B) : Onr →+* B))

    (c : ℤ)
    (hact : ModuliPackage.G.IsActBy ι Φ η Fr E₀ ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
              (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c)
        (Ξ B ψ hBπ ⟨E, ρ⟩) (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩)) :
    (t'.n : ℤ) = (t.n : ℤ) + c := by
  classical

  have ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0 := fun i => hadm'.2.2.1.constantCoeff i

  have hfrob : ∀ (a b : ℤ) (χ : Onr →ₐ[𝒪] B), frobTwist Onr Fr a (frobTwist Onr Fr b χ) = frobTwist Onr Fr (b + a) χ := by
    intro a b χ
    apply AlgHom.ext; intro z
    simp only [frobTwist, AlgHom.comp_apply, zpow_add]
    rfl

  have htr'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ' (j' + 1) t' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_succ_of_isRigTransport_frobTwist_neg_one
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ Ξ hΞleg hΞnat hΞiso hΞdef A₀r prA hprA F hF V hV F_hom V_hom F_act V_act F_lev V_lev V_F F_V V_frob
      B ψ hBπ hconn E ρ ρp ub hub hub' gA' hgA' hgA'' Fb hFb hFb' Vb hVb hVb' hd hφ hφ' X' θ' hX' j' t' ht'0 htr'
  have hadm'' : t'.IsAdmissible ι ((frobTwist Onr Fr (-((j' + 1 : ℕ) : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) := by
    have : frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr (-1) ψ) = frobTwist Onr Fr (-((j' + 1 : ℕ) : ℤ)) ψ := by
      rw [hfrob]; congr 1; push_cast; ring
    rw [this] at hadm'; exact hadm'

  obtain ⟨j₀, t₀, hj₀, ht₀X, htr₀, hadm₀, hΞ₀⟩ := hΞdef B ψ hBπ hconn hBr ⟨E, ρ⟩ X' θ' hX'
  obtain ⟨j₁, t₁, hj₁, ht₁X, htr₁, hadm₁, hΞ₁⟩ := hΞdef B (frobTwist Onr Fr (-1) ψ) hBπ hconn hBr ⟨E, ρp⟩ X' θ' hX'

  obtain ⟨hjj₀, hnn₀, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_n_eq_and_eta_eq_of_isRigTransport_of_isRigTransport
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ B ψ hBπ hconn hBr ⟨E, ρ⟩ X θ hX X' θ' hX' j t hj htX htr hadm j₀ t₀ hj₀ ht₀X htr₀ hadm₀
  obtain ⟨hjj₁, -, -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_eq_and_n_eq_and_eta_eq_of_isRigTransport_of_isRigTransport
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ B (frobTwist Onr Fr (-1) ψ) hBπ hconn hBr ⟨E, ρp⟩ X' θ' hX' X' θ' hX' j' t' hj' ht'X htr' hadm' j₁ t₁ hj₁ ht₁X htr₁ hadm₁
  subst hjj₀ hjj₁

  obtain ⟨-, hledger⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.parity_mod_two_eq_of_isRigTransport_of_isAdmissible
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr hB Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ B ψ hBπ hconn hBr ⟨E, ρ⟩ X' θ' hX' j t₀ ht₀X htr₀ hadm₀ (j' + 1) t' ht'X htr'' hadm''

  obtain ⟨e, k, m', hE, hdeg, htrans⟩ := hact
  have hleg := htrans.1
  have hψx : (Ξ B ψ hBπ ⟨E, ρ⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) ψ := by rw [hΞ₀]
  have hψx' : (Ξ B (frobTwist Onr Fr (-1) ψ) hBπ ⟨E, ρp⟩).ψ = frobTwist Onr Fr (-(j' : ℤ)) (frobTwist Onr Fr (-1) ψ) := by rw [hΞ₁]
  rw [hψx, hψx', hfrob, hfrob] at hleg
  have hlegZ : (-1 : ℤ) + -(j' : ℤ) = -(j : ℤ) + ((m' : ℤ) - 2 * k) :=
    CerednikDrinfeld.FormalOmega.eq_of_frobTwist_eq_frobTwist_of_isNilpotent_of_nontrivial π Onr Fr hOnr_closed hFr B hBπ ψ _ _ hleg

  have hrπ : Ideal.span {((r : ℕ) : Onr)} = Ideal.span {algebraMap 𝒪 Onr π} := by
    have h1 : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.subset_span rfl
    have h2 : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := by rw [hunr]; exact Ideal.subset_span rfl
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h2
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨algebraMap 𝒪 Onr u, by rw [← map_mul, hu, map_natCast]⟩
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨algebraMap 𝒪 Onr v, by rw [← map_natCast (algebraMap 𝒪 Onr), ← map_mul, hv]⟩
  have hmax : (pIdeal r Onr).IsMaximal := by
    show (Ideal.span {((r : ℕ) : Onr)}).IsMaximal
    rw [hrπ]; exact hOnr_max
  haveI : Nontrivial (Onr ⧸ pIdeal r Onr) := Ideal.Quotient.nontrivial_iff.2 hmax.ne_top
  haveI : IsNoetherianRing (Onr ⧸ pIdeal r Onr) := by
    letI : Field (Onr ⧸ pIdeal r Onr) := @Ideal.Quotient.field _ _ (pIdeal r Onr) hmax
    infer_instance
  have hpin : (2 * m' : ℤ) = 4 * ((k : ℤ) - c) :=
    CerednikDrinfeld.FormalODModule.two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree
      Φ hΦ4 E₀ hE₀.1 e k m' c hE hdeg

  omega

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_n_eq_n_add_of_isRigTransport_of_isRigTransport_frobTwist_neg_one_of_isActBy
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_n_eq_n_add_of_isRigTransport_of_isRigTransport_frobTwist_neg_one_of_isActBy (solution)

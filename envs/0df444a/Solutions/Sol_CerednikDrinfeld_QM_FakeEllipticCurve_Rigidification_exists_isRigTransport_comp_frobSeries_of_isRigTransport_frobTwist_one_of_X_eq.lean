-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isRigTransport_comp_frobSeries_of_isRigTransport_frobTwist_one_of_X_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1878708c-4f82-5652-9956-a1d168f3c312

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isRigTransport_comp_frobSeries_of_isRigTransport_frobTwist_one_of_X_eq
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace TShiftPlus46

open CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime]

theorem frob_const (R : Type) [CommRing R] (j : ℕ) (i : Fin 2) :
    MvPowerSeries.constantCoeff (frobSeries (p := p) R j i) = 0 := by
  show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ (p ^ j)) = 0
  rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem frob_comp_frob (R : Type) [CommRing R] (a b : ℕ) :
    (frobSeries (p := p) R a).comp (frobSeries (p := p) R b) = frobSeries (p := p) R (b + a) := by
  classical
  have hs : MvPowerSeries.HasSubst (frobSeries (p := p) R b) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (frob_const R b)
  funext i
  show MvPowerSeries.subst (frobSeries (p := p) R b) ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ (p ^ a)) =
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ (p ^ (b + a))
  rw [← MvPowerSeries.substAlgHom_apply hs, map_pow, MvPowerSeries.substAlgHom_X]
  show ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ (p ^ b)) ^ (p ^ a) = _
  rw [← pow_mul, ← pow_add]

theorem map_frob {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (j : ℕ) :
    Series.map f (frobSeries (p := p) R j) = frobSeries (p := p) S j := by
  funext i
  show MvPowerSeries.map f ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ (p ^ j)) = (MvPowerSeries.X i) ^ (p ^ j)
  rw [map_pow, MvPowerSeries.map_X]

theorem map_const {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (φ : Series R)
    (h : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (Series.map f φ i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, h, map_zero]

theorem map_map_series {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (φ : Series R) :
    Series.map g (Series.map f φ) = Series.map (g.comp f) φ := by
  funext i
  show MvPowerSeries.map g (MvPowerSeries.map f (φ i)) = MvPowerSeries.map (g.comp f) (φ i)
  rw [MvPowerSeries.map_comp, RingHom.comp_apply]

theorem constantCoeff_subst_of_constantCoeff_zero {σ τ R : Type} [CommRing R] [Fintype σ]
    (a : σ → MvPowerSeries τ R) (ha : ∀ l, MvPowerSeries.constantCoeff (a l) = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), finsum_eq_single _ 0]
  · simp
  · intro d hd
    have : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      simpa [map_finsuppProd, ha] using
        Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this, smul_zero]

theorem constantCoeff_comp_eq (R : Type) [CommRing R] (ψ φ : Series R) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff ((ψ.comp φ) i) = MvPowerSeries.constantCoeff (ψ i) :=
  constantCoeff_subst_of_constantCoeff_zero φ hφ (ψ i)

theorem nilEval_X_pow {B B'' : Type} [CommRing B] [CommRing B''] [Algebra B B'']
    (J : Ideal B'') (m : ℕ) (hJ : J ^ (m + 1) = ⊥) (s : Fin 2 → B'') (hs : ∀ i, s i ∈ J) (l : Fin 2) (k : ℕ) :
    MvFormalGroup.nilEval m ((MvPowerSeries.X l : MvPowerSeries (Fin 2) B) ^ k) s = (s l) ^ k := by
  classical
  unfold MvFormalGroup.nilEval
  have hn : ∀ d : Fin 2 →₀ ℕ, d ≤ Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => m) ↔ ∀ i, d i ≤ m := by
    intro d
    rw [Finsupp.le_def]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
  have hsingle : (∀ i, (Finsupp.single l k : Fin 2 →₀ ℕ) i ≤ m) ↔ k ≤ m := by
    constructor
    · intro h; simpa using h l
    · intro h i
      rw [Finsupp.single_apply]
      split_ifs
      · exact h
      · exact Nat.zero_le _
  by_cases hk : k ≤ m
  · have : MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => m) ((MvPowerSeries.X l : MvPowerSeries (Fin 2) B) ^ k) =
        (MvPolynomial.X l) ^ k := by
      ext d
      rw [MvPowerSeries.coeff_trunc', MvPowerSeries.coeff_X_pow, MvPolynomial.coeff_X_pow]
      by_cases h1 : d ≤ Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => m)
      · rw [if_pos h1]
        by_cases h2 : d = Finsupp.single l k
        · rw [if_pos h2, if_pos h2.symm]
        · rw [if_neg h2, if_neg (fun h => h2 h.symm)]
      · rw [if_neg h1]
        by_cases h3 : Finsupp.single l k = d
        · exfalso
          apply h1
          rw [← h3]
          exact (hn _).mpr (hsingle.mpr hk)
        · rw [if_neg h3]
    rw [this, map_pow, MvPolynomial.aeval_X]
  · have : MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => m) ((MvPowerSeries.X l : MvPowerSeries (Fin 2) B) ^ k) = 0 := by
      ext d
      rw [MvPowerSeries.coeff_trunc', MvPowerSeries.coeff_X_pow, MvPolynomial.coeff_zero]
      by_cases h1 : d ≤ Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => m)
      · rw [if_pos h1]
        by_cases h2 : d = Finsupp.single l k
        · exfalso
          apply hk
          apply hsingle.mp
          intro i
          rw [← h2]
          exact (hn d).mp h1 i
        · rw [if_neg h2]
      · rw [if_neg h1]
    rw [this, map_zero]
    have hmem : (s l) ^ k ∈ J ^ (m + 1) := Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (hs l) k)
    rw [hJ] at hmem
    exact ((Submodule.mem_bot _).mp hmem).symm

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

end TShiftPlus46

open TShiftPlus46 CerednikDrinfeld.SpecialFormal.Rigidified in
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
    (hprA : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π (Fr : Onr →ₐ[𝒪] Onr)) A₀ A₀r prA)
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
    (F_frob : ∀ (C : Type) [CommRing C] [CharP C r] (x : Spec (CommRingCat.of C) ⟶ A₀.A),
      x ≫ F ≫ prA = Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ x)

    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E : FakeEllipticCurve Λ N B) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (ρp : FakeEllipticCurve.Rigidification r π A₀ (frobTwist Onr Fr (1) ψ) E)
    (ub : ρ.Eb.A ⟶ ρp.Eb.A) (hub : ub ≫ ρp.gb = ρ.gb) (hub' : ub ≫ ρp.Eb.f = ρ.Eb.f)
    (gA' : ρp.Ab.A ⟶ A₀r.A) (hgA' : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀r ρp.Ab gA')
    (hgA'' : gA' ≫ prA = ρp.gA)
    (Fb : ρ.Ab.A ⟶ ρp.Ab.A) (hFb : Fb ≫ gA' = ρ.gA ≫ F) (hFb' : Fb ≫ ρp.Ab.f = ρ.Ab.f)
    (Vb : ρp.Ab.A ⟶ ρ.Ab.A) (hVb : Vb ≫ ρ.gA = gA' ≫ V) (hVb' : Vb ≫ ρ.Ab.f = ρp.Ab.f)
    (hd : ρp.d = ρ.d + 1) (hφ : ub ≫ ρp.φ = ρ.φ ≫ Fb) (hφ' : ρp.φ' = Vb ≫ ρ.φ' ≫ ub)

    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ)
    (j' : ℕ) (t' : Rigidified r Φ B) (ht'X : t'.X = X) (ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρp θ j' t') :
    ∃ t'' : Rigidified r Φ B, t''.X = t'.X ∧ (∀ i, MvPowerSeries.constantCoeff (t''.ρ i) = 0) ∧
      FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j' t'' ∧
      t'.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) = (t''.Xbar.act (r : Zp2 r)).comp t''.ρ := by
  classical
  have hr : r.Prime := Fact.out
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnΛ : ∀ n : ℕ, ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun n => by simpa using hΛℤ n

  obtain ⟨κB, σp, h1, -, hrepp, hρp⟩ := htr'
  obtain ⟨κB₂, σ, h1₂, h2₂, hOD, hrep, hT⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isODHom_isRigTransport_of_isFormalModuleVia
      coord hcoord.dense 𝒪 π hunr Onr A₀ X₀ θ₀ hA₀ κ hκ ψ ρ X θ hX
  have hκBeq : κB₂ = κB := Ideal.Quotient.ringHom_ext (h1₂.trans h1.symm)
  subst hκBeq

  have c_β₀ : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
  have c_σ : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := hOD.constantCoeff
  have c_κσ : ∀ i, MvPowerSeries.constantCoeff (Series.map κB₂ σ i) = 0 := map_const κB₂ σ c_σ
  have c_frob := frob_const (p := r) (B ⧸ pIdeal r B)
  have c_tail : ∀ (χ : Onr →+* B) (j : ℕ) (i : Fin 2), MvPowerSeries.constantCoeff
      (((Series.map (residueMap χ) β₀).comp (frobSeries (p := r) (B ⧸ pIdeal r B) j)) i) = 0 :=
    fun χ j => Series.constantCoeff_comp (map_const _ β₀ c_β₀) (c_frob j)
  have hρp' : t'.ρ = (Series.map κB₂ σp).comp ((Series.map (residueMap ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B)) β₀).comp
      (frobSeries (p := r) (B ⧸ pIdeal r B) j')) := hρp
  have c_κσp : ∀ i, MvPowerSeries.constantCoeff (Series.map κB₂ σp i) = 0 := by
    intro i
    have := ht'0 i
    rw [hρp'] at this
    rwa [constantCoeff_comp_eq _ _ _ (c_tail _ j')] at this
  have c_N₀ : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries r) i) = 0 :=
    map_const _ _ (MvFormalGroup.constantCoeff_nthSeries _ _)
  have c_κN₀ : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (Series.map κB₂ (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries r)) i) = 0 :=
    map_const _ _ c_N₀

  have hmap : Ideal.map (ψ : Onr →+* B) (Ideal.span {algebraMap 𝒪 Onr π}) = Ideal.span {algebraMap 𝒪 B π} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact ψ.commutes π
  have hrπ : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
    have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    have : ((r : ℕ) : B) = algebraMap 𝒪 B c * algebraMap 𝒪 B π := by
      rw [← map_mul, hc, map_natCast]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

  have hcore : ∀ y : Onr, ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) y - (ψ : Onr →+* B) y ^ r ∈
      Ideal.span {algebraMap 𝒪 B π} := by
    intro y
    have hFy : (Fr ^ (1 : ℤ)) y = Fr y := by rw [zpow_one]
    have e1 : ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) y = (ψ : Onr →+* B) ((Fr ^ (1 : ℤ)) y) := rfl
    have e2 : (ψ : Onr →+* B) ((Fr ^ (1 : ℤ)) y) - (ψ : Onr →+* B) y ^ r = (ψ : Onr →+* B) (Fr y - y ^ r) := by
      rw [map_sub, map_pow, hFy]
    rw [e1, e2, ← hmap]
    exact Ideal.mem_map_of_mem _ (hFr _)
  have hχ : ∀ x : Onr ⧸ pIdeal r Onr, residueMap ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) x =
      (residueMap (ψ : Onr →+* B) x) ^ (r ^ 1) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pow_one]
    show Ideal.Quotient.mk _ (((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) y) = (Ideal.Quotient.mk _ ((ψ : Onr →+* B) y)) ^ r
    rw [← map_pow, Ideal.Quotient.eq]
    have hπr : Ideal.span {algebraMap 𝒪 B π} ≤ pIdeal r B := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have : π ∈ Ideal.span {((r : ℕ) : 𝒪)} := hunr ▸ Ideal.subset_span rfl
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
      rw [← hc, map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    exact hπr (hcore y)

  have key : (Series.map κB₂ σp).comp (frobSeries (p := r) (B ⧸ pIdeal r B) 1) =
      (Series.map κB₂ σ).comp (Series.map κB₂ (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries r))) := by
    apply GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
      E.L X.F θ hX.1 (pIdeal r B) _ _ (fun i => Series.constantCoeff_comp c_κσp (c_frob 1) i) (fun i => Series.constantCoeff_comp c_κσ c_κN₀ i)
    intro B'' _ _ _ hc J m hJ s hs

    letI instπ : Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'' := ((algebraMap (B ⧸ pIdeal r B) B'').comp κB₂).toAlgebra
    have hκc : algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'' = (algebraMap (B ⧸ pIdeal r B) B'').comp κB₂ := rfl
    have hcπ : algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) := by
      rw [hc, hκc, RingHom.comp_assoc, h1₂]

    let lp : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* B'' :=
      (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)
    let lpp : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* B'' :=
      (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp
        (FakeEllipticCurve.Rigidification.residueLeg π (frobTwist Onr Fr (1) ψ))
    letI instO : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' := lp.toAlgebra
    have hc2 : algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
        (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) := rfl

    set s₁ : Fin 2 → B'' := fun l => MvFormalGroup.nilEval m (X₀.F.nthSeries r l) s with hs₁
    have hs₁J : ∀ l, s₁ l ∈ J := fun l =>
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs (X₀.F.nthSeries r) (MvFormalGroup.constantCoeff_nthSeries _ _)
        (0 : MvPowerSeries (Fin 2) _)).1 l

    have eL : (fun i => MvFormalGroup.nilEval m (((Series.map κB₂ σp).comp (frobSeries (p := r) (B ⧸ pIdeal r B) 1)) i) s) =
        fun i => MvFormalGroup.nilEval m (σp i) (fun l => s l ^ r) := by
      funext i
      show MvFormalGroup.nilEval m (MvPowerSeries.subst (frobSeries (p := r) (B ⧸ pIdeal r B) 1)
        (MvPowerSeries.map κB₂ (σp i))) s = _
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ (c_frob 1) _).2, nilEval_map_of_algebraMap_eq κB₂ hκc]
      congr 1
      funext l
      show MvFormalGroup.nilEval m ((MvPowerSeries.X l : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ 1)) s = _
      rw [nilEval_X_pow J m hJ s hs, pow_one]
    have eR : (fun i => MvFormalGroup.nilEval m (((Series.map κB₂ σ).comp
          (Series.map κB₂ (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries r)))) i) s) =
        fun i => MvFormalGroup.nilEval m (σ i) s₁ := by
      funext i
      show MvFormalGroup.nilEval m (MvPowerSeries.subst
        (Series.map κB₂ (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries r)))
        (MvPowerSeries.map κB₂ (σ i))) s = _
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ c_κN₀ _).2, nilEval_map_of_algebraMap_eq κB₂ hκc]
      congr 1
      funext l
      show MvFormalGroup.nilEval m (MvPowerSeries.map κB₂ (MvPowerSeries.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)
        (X₀.F.nthSeries r l))) s = _
      rw [nilEval_map_of_algebraMap_eq κB₂ hκc, nilEval_map_of_algebraMap_eq _ hc2, hs₁]
    rw [eL, eR]

    rcases subsingleton_or_nontrivial B'' with hB'' | hB''
    · congr 1
      exact funext fun _ => Subsingleton.elim _ _
    haveI : CharP B'' r := (CharP.charP_iff_prime_eq_zero hr).mpr (by
      have : ((r : ℕ) : B'') = algebraMap B B'' (r : B) := by rw [map_natCast]
      rw [this, hcπ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hrπ, map_zero])
    have hsr : ∀ l, s l ^ r ∈ J := fun l => Ideal.pow_mem_of_mem J (hs l) r hr.pos
    have hsnil : ∀ i, IsNilpotent (s i) := fun i => ⟨m + 1, by
      have := Ideal.pow_mem_pow (hs i) (m + 1)
      rw [hJ] at this
      exact (Submodule.mem_bot _).mp this⟩

    obtain ⟨PA, hPAf, hPAg⟩ : ∃ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
        PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) ∧
        PA ≫ ρ.gA = (θ₀ B'' s).1 := by
      obtain ⟨hsq, -⟩ := ρ.isPullback_Ab
      have hw : (θ₀ B'' s).1 ≫ A₀.f =
          Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) ≫
            Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) := by
        rw [(θ₀ B'' s).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact ⟨hsq.lift _ _ hw, hsq.lift_snd _ _ hw, hsq.lift_fst _ _ hw⟩

    have hcomm : ∀ x : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}, frobenius B'' r (lp x) = lpp x := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      show ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'') (Ideal.Quotient.mk _ ((ψ : Onr →+* B) y))) ^ r =
        (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')
          (Ideal.Quotient.mk _ (((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) y))
      rw [← map_pow, ← map_pow]
      congr 1
      rw [eq_comm, Ideal.Quotient.eq]
      exact hcore y
    let φF := @AlgHom.mk (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' B'' _ _ _ instO lpp.toAlgebra
      (frobenius B'' r) (fun x => hcomm x)
    have hnat0 := hA₀.1.1
    have hPApf : (PA ≫ Fb) ≫ ρp.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) := by
      rw [Category.assoc, hFb', hPAf]
    have hPApA : (PA ≫ Fb) ≫ ρp.gA = (@θ₀ B'' _ lpp.toAlgebra (fun l => s l ^ r)).1 := by
      have hnat := @hnat0 B'' _ instO B'' _ lpp.toAlgebra φF s hsnil
      have hfs : (fun l => s l ^ r) = (φF : B'' → B'') ∘ s := funext fun l => rfl
      rw [hfs, hnat]
      show (PA ≫ Fb) ≫ ρp.gA = Spec.map (CommRingCat.ofHom (frobenius B'' r)) ≫ (θ₀ B'' s).1
      have e3 : (PA ≫ Fb) ≫ ρp.gA = (PA ≫ ρ.gA) ≫ F ≫ prA := by
        rw [← hgA'', Category.assoc, ← Category.assoc Fb gA' prA, hFb]
        simp only [Category.assoc]
      rw [e3, F_frob B'' (PA ≫ ρ.gA), hPAg]
    have hL1 : (PA ≫ Fb) ≫ ρp.φ' ≫ ρp.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σp i) (fun l => s l ^ r))).1 := by
      exact @hrepp B'' _ _ _ lpp.toAlgebra hcπ rfl J m hJ _ hsr (PA ≫ Fb) hPApf hPApA

    have hQf : (PA ≫ Fb ≫ Vb) ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) := by
      simp only [Category.assoc]
      rw [hVb', hFb', hPAf]
    have hQA : (PA ≫ Fb ≫ Vb) ≫ ρ.gA = (θ₀ B'' s₁).1 := by
      have hINT0 := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
        A₀ coord hcoord X₀ θ₀ hA₀ h1Λ r (hnΛ r) B'' J m hJ s hs
      rw [MvFormalGroup.End.toPowerSeries_natCast] at hINT0
      have hVF := congrArg Subtype.val (V_F _ (θ₀ B'' s))
      rw [mapPt_coe, mapPt_coe, ← CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt A₀ h1Λ r (hnΛ r)] at hVF
      have e4 : (PA ≫ Fb ≫ Vb) ≫ ρ.gA = ((θ₀ B'' s).1 ≫ F) ≫ V := by
        rw [← hPAg]
        simp only [Category.assoc]
        rw [hVb, ← Category.assoc Fb gA' V, hFb]
        simp only [Category.assoc]
      rw [e4, hVF, hs₁, hINT0]
    have hR1 : (PA ≫ Fb ≫ Vb) ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s₁)).1 := by
      exact hrep B'' hcπ hc2 J m hJ s₁ hs₁J _ hQf hQA
    apply Subtype.ext
    rw [← hL1, ← hR1, hφ']
    simp only [Category.assoc, hub]

  have key' : (Series.map κB₂ σp).comp (frobSeries (p := r) (B ⧸ pIdeal r B) 1) =
      (Series.map (Ideal.Quotient.mk (pIdeal r B)) (X.act (r : Zp2 r))).comp (Series.map κB₂ σ) := by
    have e7 := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
      π hΛℤ coord hcoord A₀ X₀ θ₀ hA₀ ψ E X θ hX ρ σ c_σ hrep r
    have c_N : ∀ i : Fin 2, MvPowerSeries.constantCoeff
        (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (X.F.nthSeries r) i) = 0 :=
      map_const _ _ (MvFormalGroup.constantCoeff_nthSeries _ _)
    rw [key, FormalODModule.act_natCast, ← h1₂, ← map_map_series, ← Series.map_comp κB₂ _ _ c_σ, e7,
      Series.map_comp κB₂ _ _ c_N₀]

  refine ⟨{ X := X, n := t'.n,
            ρ := (Series.map κB₂ σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
              (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j'))) },
    ht'X.symm, fun i => Series.constantCoeff_comp c_κσ (c_tail _ j') i, hT Φ β₀ j' t'.n, ?_⟩
  rw [hρp']
  show ((Series.map κB₂ σp).comp ((Series.map (residueMap ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B)) β₀).comp
      (frobSeries (p := r) (B ⧸ pIdeal r B) j'))).comp (frobSeries (p := r) (B ⧸ pIdeal r B) 1) =
    (Series.map (Ideal.Quotient.mk (pIdeal r B)) (X.act (r : Zp2 r))).comp
      ((Series.map κB₂ σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (frobSeries (p := r) (B ⧸ pIdeal r B) j')))
  rw [Series.comp_assoc _ _ _ (c_tail _ j') (c_frob 1), Series.comp_assoc _ _ _ (c_frob j') (c_frob 1), frob_comp_frob,
    show 1 + j' = j' + 1 from Nat.add_comm 1 j', ← frob_comp_frob (p := r) (B ⧸ pIdeal r B) 1 j',
    ← Series.comp_assoc _ _ _ (c_frob 1) (c_frob j'),
    ← CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
      ((frobTwist Onr Fr (1) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) (ψ : Onr →+* B) 1 hχ β₀ c_β₀,
    Series.comp_assoc _ _ _ (map_const _ β₀ c_β₀) (c_frob j'),
    ← Series.comp_assoc _ (frobSeries (p := r) _ 1) _ (c_frob 1) (c_tail _ j'), key',
    Series.comp_assoc _ _ _ c_κσ (c_tail _ j')]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isRigTransport_comp_frobSeries_of_isRigTransport_frobTwist_one_of_X_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isRigTransport_comp_frobSeries_of_isRigTransport_frobTwist_one_of_X_eq (solution)

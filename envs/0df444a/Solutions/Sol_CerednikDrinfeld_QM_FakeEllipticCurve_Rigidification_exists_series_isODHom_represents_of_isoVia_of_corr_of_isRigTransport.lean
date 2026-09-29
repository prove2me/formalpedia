-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/31e31c61-b7d0-55d1-83b4-7b395dff363c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleVia_mapPt_of_iso
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isODHom_isRigTransport_of_isFormalModuleVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace N2Series

theorem act_congr {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N S)
    {x y : ℍ[ℚ, a, b]} (h : x = y) (hx : x ∈ Λ) (hy : y ∈ Λ) : E.act ⟨x, hx⟩ = E.act ⟨y, hy⟩ := by
  subst h; rfl

theorem act_natCast_comp {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (E : FakeEllipticCurve Λ N S) (m n : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (hnm : (((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    E.act ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ ≫ E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ = E.act ⟨(((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnm⟩ := by
  have h : ((n : ℚ) : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) * ((m : ℚ) : ℍ[ℚ, a, b]) = (((n * m : ℕ) : ℚ) : ℍ[ℚ, a, b]) := by push_cast; rfl
    rw [this]; exact hnm
  rw [← E.act_mul ⟨((n : ℚ) : ℍ[ℚ, a, b]), hn⟩ ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩ h]
  exact act_congr E (by push_cast; rfl) _ _

theorem constantCoeff_subst_of_forall {σ τ : Type} [Finite σ] {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {a : σ → MvPowerSeries τ S} (ha : MvPowerSeries.HasSubst a) (ha' : ∀ i, (a i).constantCoeff = 0)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = algebraMap R S (f.constantCoeff) := by
  classical
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp [Algebra.smul_def]
  · intro d hd
    have : MvPowerSeries.constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      simp [map_finsuppProd, ha']
      exact Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this, smul_zero]

theorem nilEval_sub {σ : Type} [Fintype σ] [DecidableEq σ] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (n : ℕ) (φ ψ : MvPowerSeries σ R) (s : σ → R') :
    MvFormalGroup.nilEval n (φ - ψ) s = MvFormalGroup.nilEval n φ s - MvFormalGroup.nilEval n ψ s := by
  unfold MvFormalGroup.nilEval
  rw [map_sub, map_sub]

theorem corr_exponent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B}
    (E E' : FakeEllipticCurve Λ N B) (i : E.A ≅ E'.A)
    (ϱ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ϱ' : FakeEllipticCurve.Rigidification r π A₀ ψ E')
    (ib : ϱ.Eb.A ⟶ ϱ'.Eb.A)
    (uA : ϱ'.Ab.A ⟶ ϱ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ϱ.Ab ϱ'.Ab uA)
    (i₁ j₁ : ℕ)
    (hcorr : ib ≫ ϱ'.φ ≫ uA ≫ ϱ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ϱ.φ ≫ ϱ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) :
    ϱ'.φ' ≫ ϱ'.Eb.act ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ ϱ.φ' ≫ ib ≫ ϱ'.Eb.act ⟨(((r ^ ϱ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ := by

  set cI : ↥Λ := ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcI
  set cJ : ↥Λ := ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcJ
  set cD : ↥Λ := ⟨(((r ^ ϱ.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcD
  set cD' : ↥Λ := ⟨(((r ^ ϱ'.d : ℕ) : ℤ) : ℚ), hΛℤ _⟩ with hcD'

  obtain ⟨hφo, hψo, -, -, hlinφ, hlinψ, hcomp⟩ := ϱ.isIsogenyPair
  obtain ⟨hφo', hψo', -, -, hlinφ', hlinψ', hcomp'⟩ := ϱ'.isIsogenyPair
  have hdmem : (((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ ϱ.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hdmem' : (((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have := hΛℤ ((r ^ ϱ'.d : ℕ) : ℤ); rwa [Int.cast_natCast] at this
  have hcD_eq : (⟨(((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdmem⟩ : ↥Λ) = cD := Subtype.ext (by simp [hcD])
  have hcD'_eq : (⟨(((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hdmem'⟩ : ↥Λ) = cD' := Subtype.ext (by simp [hcD'])
  obtain ⟨h1, h2⟩ := hcomp hdmem
  obtain ⟨h1', h2'⟩ := hcomp' hdmem'
  rw [hcD_eq] at h1 h2
  rw [hcD'_eq] at h1' h2'

  obtain ⟨hsq, -, hlinuA, -⟩ := huA
  have hw : 𝟙 ϱ.Ab.A ≫ ϱ.Ab.f = ϱ.Ab.f ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) := by simp
  set v : ϱ.Ab.A ⟶ ϱ'.Ab.A := hsq.lift (𝟙 _) ϱ.Ab.f hw with hv
  have hvu : v ≫ uA = 𝟙 _ := hsq.lift_fst _ _ _
  have hvf : v ≫ ϱ'.Ab.f = ϱ.Ab.f := hsq.lift_snd _ _ _
  have huv : uA ≫ v = 𝟙 _ := by
    apply hsq.hom_ext
    · rw [Category.assoc, hvu, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hvf, Category.id_comp]; simpa using hsq.w
  have hlinv : ∀ x : ↥Λ, ϱ.Ab.act x ≫ v = v ≫ ϱ'.Ab.act x := by
    intro x
    calc ϱ.Ab.act x ≫ v = (v ≫ uA) ≫ ϱ.Ab.act x ≫ v := by rw [hvu, Category.id_comp]
      _ = v ≫ (uA ≫ ϱ.Ab.act x) ≫ v := by simp only [Category.assoc]
      _ = v ≫ (ϱ'.Ab.act x ≫ uA) ≫ v := by rw [hlinuA x]
      _ = v ≫ ϱ'.Ab.act x ≫ (uA ≫ v) := by simp only [Category.assoc]
      _ = v ≫ ϱ'.Ab.act x := by rw [huv, Category.comp_id]

  have step1 : ib ≫ ϱ'.Eb.act cD' ≫ ϱ'.Eb.act cI = ϱ.φ ≫ v ≫ ϱ'.φ' ≫ ϱ'.Eb.act cJ := by
    have := congrArg (fun f => f ≫ v ≫ ϱ'.φ') hcorr
    simp only [Category.assoc] at this

    rw [← Category.assoc (ϱ.Ab.act cI) v, hlinv cI, Category.assoc, ← Category.assoc uA v, huv, Category.id_comp,
      hlinψ' cI, ← Category.assoc ϱ'.φ ϱ'.φ', h1', ← Category.assoc (ϱ.Ab.act cJ) v, hlinv cJ, Category.assoc,
      hlinψ' cJ] at this
    exact this

  have step2 := congrArg (fun f => uA ≫ ϱ.φ' ≫ f) step1

  rw [← Category.assoc ϱ.φ' ϱ.φ, h2, ← Category.assoc (ϱ.Ab.act cD) v, hlinv cD, Category.assoc,
    ← Category.assoc uA v, huv, Category.id_comp] at step2
  rw [← Category.assoc (ϱ'.Ab.act cD), hlinψ' cD, Category.assoc] at step2
  exact step2.symm

end N2Series

open N2Series in
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

    (Q : Spec (CommRingCat.of (B ⧸ Ideal.span {algebraMap 𝒪 B π})) ⟶ ϱ.Ab.A) (hQf : Q ≫ ϱ.Ab.f = 𝟙 _)
    (hQg : Q ≫ ϱ.gA = Spec.map (CommRingCat.ofHom (FakeEllipticCurve.Rigidification.residueLeg π ψ)) ≫ (P₀.P).1)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hXθ : E.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (hlev : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) ≫ (nsmulPt E.L (𝟙 _) (r ^ t.n) Pn.P).1 =
      Q ≫ ϱ.φ' ≫ ϱ.gb)

    (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B)) (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B))
    (hκBψ : κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ)
    (hσ : ∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ϱ.Ab.A,
            PA ≫ ϱ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ϱ.gA = (θ₀ B'' s).1 →
              PA ≫ ϱ.φ' ≫ ϱ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1)
    (htρ : t.ρ = (Series.map κB σ).comp
      ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))))
    :
    ∃ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}),

      FormalODModule.IsODHom (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ' ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ ϱ'.Ab.A,
              PA ≫ ϱ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ ϱ'.gA = (θ₀ B'' s).1 →
                PA ≫ ϱ'.φ' ≫ ϱ'.gb = (mapPt i.hom hi (θ B'' (fun i => MvFormalGroup.nilEval m (σ' i) s))).1) ∧

      (((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ' = ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) := by
  classical
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := by simpa using hΛℤ 1
  have hnat : ∀ m : ℕ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := fun m => by
    have := hΛℤ (m : ℤ); rwa [Int.cast_natCast] at this

  have hXθ' := CerednikDrinfeld.QM.FakeEllipticCurve.IsFormalModuleVia.mapPt_of_iso coord B E E' i hi hiso.1 hiso.2.1 X θ hXθ

  obtain ⟨κB', σ', hκB'1, hκB'2, hOD', hrep', -⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isODHom_isRigTransport_of_isFormalModuleVia
      coord hcoord.dense 𝒪 π hunr Onr A₀ X₀ θ₀ hA₀ κ hκ ψ ϱ' X _ hXθ'
  refine ⟨σ', hOD', hrep', ?_⟩

  have hI := corr_exponent hΛℤ E E' i ϱ ϱ' ib uA huA i₁ j₁ hcorr
  obtain ⟨hsqA, muA, auA, luA⟩ := huA
  obtain ⟨hgb, mgb, agb, lgb⟩ := ϱ'.isPullback_Eb
  obtain ⟨hφo, hφ'o, mφ, mφ', aφ, aφ', cφ⟩ := ϱ'.isIsogenyPair
  have hsid' : Spec.map (CommRingCat.ofHom (RingHom.id (B ⧸ Ideal.span {algebraMap 𝒪 B π}))) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _

  letI algA : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
    (FakeEllipticCurve.Rigidification.residueLeg π ψ).toAlgebra
  obtain ⟨θA, hθA, hθAg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) A₀ ϱ'.Ab ϱ'.gA ϱ'.isPullback_Ab X₀ θ₀ hA₀

  have hgb' : FakeEllipticCurve.IsPullbackVia (algebraMap B (B ⧸ Ideal.span {algebraMap 𝒪 B π})) E' ϱ'.Eb ϱ'.gb := by
    rw [Ideal.Quotient.algebraMap_eq]; exact ϱ'.isPullback_Eb
  obtain ⟨θEb, hθEb, hθEbg⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq coord
      B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) E' ϱ'.Eb ϱ'.gb hgb' X _ hXθ'
  rw [Ideal.Quotient.algebraMap_eq] at hθEb

  have hσ'0 : ∀ j, MvPowerSeries.constantCoeff (σ' j) = 0 := hOD'.constantCoeff
  have hσ0 : ∀ j, MvPowerSeries.constantCoeff (σ j) = 0 := by

    intro j0
    obtain ⟨-, -, hisoρ⟩ := hadm
    have hρ0 := hisoρ.1.constantCoeff j0
    rw [htρ] at hρ0

    have hβ00 : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
    have hγ0 : ∀ i, MvPowerSeries.constantCoeff (((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) i) = 0 := by
      intro i
      show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ _) = 0
      apply MvPowerSeries.constantCoeff_subst_eq_zero
      · apply MvPowerSeries.hasSubst_of_constantCoeff_zero
        intro l; rw [map_pow, MvPowerSeries.constantCoeff_X]; exact zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
      · intro l; rw [map_pow, MvPowerSeries.constantCoeff_X]; exact zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
      · show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
        rw [MvPowerSeries.constantCoeff_map, hβ00, map_zero]
    have hγS : MvPowerSeries.HasSubst ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
    have e1 : MvPowerSeries.constantCoeff (((Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j)))) j0) =
        κB (MvPowerSeries.constantCoeff (σ j0)) := by
      show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (MvPowerSeries.map κB (σ j0))) = _
      rw [constantCoeff_subst_of_forall hγS hγ0, MvPowerSeries.constantCoeff_map]
      rfl
    rw [e1] at hρ0

    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (MvPowerSeries.constantCoeff (σ j0))
    rw [← hx] at hρ0 ⊢
    have : Ideal.Quotient.mk (pIdeal r B) x = 0 := by
      rw [← hκB]; exact hρ0
    rw [Ideal.Quotient.eq_zero_iff_mem] at this ⊢
    have hr : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
      have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := hunr ▸ Ideal.subset_span rfl
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
      rw [Ideal.mem_span_singleton']
      exact ⟨algebraMap 𝒪 B c, by rw [← map_mul, hc, map_natCast]⟩
    have hle : pIdeal r B ≤ Ideal.span {algebraMap 𝒪 B π} := by
      rw [show pIdeal r B = Ideal.span {((r : ℕ) : B)} from rfl, Ideal.span_le]; simpa using hr
    exact hle this

  have key : ∀ (C : Type) [CommRing C] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C] (J : Ideal C) (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → C, (∀ i, s i ∈ J) →
        (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ') i) s) =
        (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) i) s) := by
    intro C _ _ J m hJ s hs
    letI algBC : Algebra B C := ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (Ideal.Quotient.mk _)).toAlgebra
    letI algOC : Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) C :=
      ((algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C).comp (FakeEllipticCurve.Rigidification.residueLeg π ψ)).toAlgebra
    haveI : IsScalarTower B (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have hnil : ∀ (u : Fin 2 → C), (∀ i, u i ∈ J) → ∀ i, IsNilpotent (u i) := fun u hu i =>
      ⟨m + 1, by have := Ideal.pow_mem_pow (hu i) (m + 1); rw [hJ] at this; exact this⟩

    have hσ's : ∀ i, MvFormalGroup.nilEval m (σ' i) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ' hσ'0 (0 : MvPowerSeries (Fin 2) (B ⧸ Ideal.span {algebraMap 𝒪 B π}))).1
    have hσs : ∀ i, MvFormalGroup.nilEval m (σ i) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσ0 (0 : MvPowerSeries (Fin 2) (B ⧸ Ideal.span {algebraMap 𝒪 B π}))).1

    have hcomp : ∀ (k : ℕ) (τ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (hτ : ∀ i, MvPowerSeries.constantCoeff (τ i) = 0) (i : Fin 2),
        MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ k)).comp τ) i) s =
          MvFormalGroup.nilEval m ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ k) i) (fun l => MvFormalGroup.nilEval m (τ l) s) :=
      fun k τ hτ i => (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs τ hτ _).2

    have hact : ∀ (k : ℕ) (u : Fin 2 → C), (∀ i, u i ∈ J) →
        θEb C (fun i => MvFormalGroup.nilEval m ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ k) i) u) =
          mapPt (ϱ'.Eb.act ⟨(((r ^ k : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩) (ϱ'.Eb.act_over _) (θEb C u) := by
      intro k u hu
      have h := CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
        ϱ'.Eb coord hcoord (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) θEb hθEb h1Λ (r ^ k) (hnat _) C J m hJ u hu
      rw [← h, ← Nat.cast_pow, FormalODModule.act_natCast, MvFormalGroup.End.toPowerSeries_natCast]

    have hsn := hnil s hs
    have hPAf : (θA C s).1 ≫ ϱ'.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)) := (θA C s).2
    have hPAg : (θA C s).1 ≫ ϱ'.gA = (θ₀ C s).1 := hθAg C s hsn

    have e1 : (θA C s).1 ≫ ϱ'.φ' = (θEb C (fun l => MvFormalGroup.nilEval m (σ' l) s)).1 := by
      have h1 := hrep' C rfl rfl J m hJ s hs (θA C s).1 hPAf hPAg
      have h2 := hθEbg C (fun l => MvFormalGroup.nilEval m (σ' l) s) (hnil _ hσ's)
      apply hgb.hom_ext
      · rw [Category.assoc, h1, h2]
      · rw [Category.assoc, hφ'o, hPAf, (θEb C _).2]

    have e2 : (θA C s).1 ≫ uA ≫ ϱ.φ' ≫ ib = (θEb C (fun l => MvFormalGroup.nilEval m (σ l) s)).1 := by
      have hPA2f : ((θA C s).1 ≫ uA) ≫ ϱ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) C)) := by
        rw [Category.assoc, hsqA.w, hsid', Category.comp_id, hPAf]
      have hPA2g : ((θA C s).1 ≫ uA) ≫ ϱ.gA = (θ₀ C s).1 := by rw [Category.assoc, huAg, hPAg]
      have h3 := hσ C rfl rfl J m hJ s hs ((θA C s).1 ≫ uA) hPA2f hPA2g
      have h4 := hθEbg C (fun l => MvFormalGroup.nilEval m (σ l) s) (hnil _ hσs)
      apply hgb.hom_ext
      · simp only [Category.assoc]
        rw [hibg, h4, mapPt_coe, ← h3]
        simp only [Category.assoc]
      · obtain ⟨hgbE, -, -, -⟩ := ϱ.isPullback_Eb
        simp only [Category.assoc]
        rw [hibf, (θEb C _).2]

        obtain ⟨-, hφ'oE, -, -, -, -, -⟩ := ϱ.isIsogenyPair
        rw [hφ'oE, ← Category.assoc, hPA2f]

    have eL : (θEb C (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ') i) s)).1 =
        (θA C s).1 ≫ ϱ'.φ' ≫ ϱ'.Eb.act ⟨(((r ^ (ϱ.d + j₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
      have : (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ') i) s) =
          (fun i => MvFormalGroup.nilEval m ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁)) i)
            (fun l => MvFormalGroup.nilEval m (σ' l) s)) := funext (hcomp _ σ' hσ'0)
      rw [this, hact _ _ hσ's, mapPt_coe, ← e1, Category.assoc]
    have eR : (θEb C (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) i) s)).1 =
        (θA C s).1 ≫ uA ≫ ϱ.φ' ≫ ib ≫ ϱ'.Eb.act ⟨(((r ^ (ϱ'.d + i₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
      have : (fun i => MvFormalGroup.nilEval m ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) i) s) =
          (fun i => MvFormalGroup.nilEval m ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁)) i)
            (fun l => MvFormalGroup.nilEval m (σ l) s)) := funext (hcomp _ σ hσ0)
      rw [this, hact _ _ hσs, mapPt_coe, ← e2]
      simp only [Category.assoc]

    have eD : ∀ (m : ℕ), ϱ'.Eb.act ⟨(((r ^ m : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
        ϱ'.Eb.act ⟨((((r ^ m : ℕ) : ℤ) : ℚ) : ℍ[ℚ, a, b]), hΛℤ _⟩ :=
      fun m => act_congr ϱ'.Eb (by rw [Int.cast_natCast]) _ _
    have hI2 : ϱ'.φ' ≫ ϱ'.Eb.act ⟨(((r ^ (ϱ.d + j₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
        uA ≫ ϱ.φ' ≫ ib ≫ ϱ'.Eb.act ⟨(((r ^ (ϱ'.d + i₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
      have hc1 : ϱ'.Eb.act ⟨(((r ^ (ϱ.d + j₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
          ϱ'.Eb.act ⟨(((r ^ ϱ.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ j₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
        rw [act_natCast_comp ϱ'.Eb (r ^ ϱ.d) (r ^ j₁) (hnat _) (hnat _) (hnat _)]
        exact act_congr ϱ'.Eb (by rw [pow_add, mul_comm]) _ _
      have hc2 : ϱ'.Eb.act ⟨(((r ^ (ϱ'.d + i₁) : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ =
          ϱ'.Eb.act ⟨(((r ^ ϱ'.d : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ ≫ ϱ'.Eb.act ⟨(((r ^ i₁ : ℕ) : ℚ) : ℍ[ℚ, a, b]), hnat _⟩ := by
        rw [act_natCast_comp ϱ'.Eb (r ^ ϱ'.d) (r ^ i₁) (hnat _) (hnat _) (hnat _)]
        exact act_congr ϱ'.Eb (by rw [pow_add, mul_comm]) _ _
      rw [hc1, hc2, eD, eD, eD, eD]
      exact hI

    have hinj := ((hθEb.1).2 C J m hJ).2.1
    apply hinj
    · intro i
      rw [hcomp _ σ' hσ'0]
      exact (MvFormalGroup.nilEval_subst_of_mem J m hJ _ hσ's _ (fun l => (FormalODModule.IsODHom.act_natCast_pow (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) _).constantCoeff l) 0).1 i
    · intro i
      rw [hcomp _ σ hσ0]
      exact (MvFormalGroup.nilEval_subst_of_mem J m hJ _ hσs _ (fun l => (FormalODModule.IsODHom.act_natCast_pow (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) _).constantCoeff l) 0).1 i
    · apply Subtype.ext
      rw [eL, eR, hI2]

  funext i0
  rw [← sub_eq_zero]
  have hmem := MvFormalGroup.mem_span_of_forall_nilEval_eq_zero (B := (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (∅ : Set (MvPowerSeries (Fin 2) (B ⧸ Ideal.span {algebraMap 𝒪 B π})))
    (((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ') i0) - ((((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) i0))
    (by
      intro C _ _ J m hJ s hs _
      rw [nilEval_sub, sub_eq_zero]
      exact congrFun (key C J m hJ s hs) i0)
  simpa using hmem

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_series_isODHom_represents_of_isoVia_of_corr_of_isRigTransport (solution)

-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1b94a0ef-474b-52bb-995f-3dee55b193c6

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_of_comp_left
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasHeight_hasKernelOfDegree_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_dvd_of_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace N2Height

open MvPowerSeries in

theorem constantCoeff_subst_of_constantCoeff_zero {σ τ R : Type} [CommRing R]
    (a : σ → MvPowerSeries τ R) (ha : ∀ s, constantCoeff (a s) = 0) [Finite σ] (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsplit : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  conv_lhs => rw [hsplit]
  rw [← coe_substAlgHom hs, map_add, map_add, coe_substAlgHom hs,
    constantCoeff_subst_eq_zero hs ha h0, zero_add, subst_C, constantCoeff_C]

end N2Height

open N2Height in
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
    (B : Type) [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))

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
    ∀ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π}),
      FormalODModule.IsODHom (X₀.map (FakeEllipticCurve.Rigidification.residueLeg π ψ)) (X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))) σ' →
      (((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ' = ((X.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) →
        ∃ n' : ℕ, n' + (ϱ.d + j₁) = t.n + (ϱ'.d + i₁) ∧
          FormalODModule.IsIsogenyOfHeight
            (Φ.map (residueMap ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B)))
            (X.map (Ideal.Quotient.mk (pIdeal r B)))
            ((Series.map κB σ').comp
            ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
              (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))))
            (4 * n') := by
  classical
  intro σ' hOD hid
  subst htX
  have hrp : r.Prime := Fact.out

  set mkπ : B →+* B ⧸ Ideal.span {algebraMap 𝒪 B π} := Ideal.Quotient.mk _ with hmkπ
  set mkr : B →+* B ⧸ pIdeal r B := Ideal.Quotient.mk _ with hmkr
  set ψr : Onr →+* B := (ψ : Onr →+* B) with hψr
  set ψj : Onr →+* B := ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) with hψj
  set frob : Series (B ⧸ pIdeal r B) := fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j) with hfrob
  set β₀ψ : Series (B ⧸ pIdeal r B) := Series.map (residueMap ψr) β₀ with hβ₀ψ

  obtain ⟨cr, hcr⟩ : ∃ c : 𝒪, c * π = (r : 𝒪) := Ideal.mem_span_singleton'.mp (hunr ▸ Ideal.subset_span rfl)
  obtain ⟨cπ, hcπ⟩ : ∃ c : 𝒪, c * (r : 𝒪) = π := Ideal.mem_span_singleton'.mp (hunr.symm ▸ Ideal.subset_span rfl)
  have hrB : (r : B) = algebraMap 𝒪 B cr * algebraMap 𝒪 B π := by
    rw [← map_mul, hcr, map_natCast]
  have hπB : algebraMap 𝒪 B π = algebraMap 𝒪 B cπ * (r : B) := by
    rw [← map_natCast (algebraMap 𝒪 B) r, ← map_mul, hcπ]

  haveI hBr : Nontrivial (B ⧸ pIdeal r B) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun htop => ?_)
    have hu : IsUnit (r : B) := (Ideal.span_singleton_eq_top).mp htop
    have hn : IsNilpotent (r : B) := by
      rw [hrB]; exact Commute.isNilpotent_mul_left (Commute.all _ _) hB
    obtain ⟨k, hk⟩ := hn
    have := (hu.pow k)
    rw [hk, isUnit_zero_iff] at this
    exact zero_ne_one this

  have hκinj : ∀ x, κB x = 0 → x = 0 := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : κB (Ideal.Quotient.mk _ b) = mkr b := by
      show (κB.comp (Ideal.Quotient.mk _)) b = _; rw [hκB]
    rw [h1, hmkr, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hc, hrB, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

  obtain ⟨-, hX4, hρ⟩ := hadm
  have hρ0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := hρ.1.constantCoeff

  have hq : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π}) ∘ Fr =
      fun x => (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π}) x) ^ r := by
    funext x
    show Ideal.Quotient.mk _ (Fr x) = Ideal.Quotient.mk _ (x ^ r)
    exact (Ideal.Quotient.eq).mpr (hFr x)
  have hqk : ∀ (k : ℕ) (z : Onr), Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π}) ((Fr ^ k) z) =
      (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π}) z) ^ (r ^ k) := by
    intro k z
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply, pow_zero, pow_one]
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, show Ideal.Quotient.mk _ (Fr ((Fr ^ k) z)) = _ from congrFun hq ((Fr ^ k) z), ih,
        ← pow_mul, pow_succ]
  have hψπ : ∀ z : Onr, z ∈ Ideal.span {algebraMap 𝒪 Onr π} → ψr z ∈ pIdeal r B := by
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    show (ψ : Onr →+* B) (a * algebraMap 𝒪 Onr π) ∈ Ideal.span {(r : B)}
    rw [map_mul, show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π, hπB, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hg : ∀ x : Onr ⧸ pIdeal r Onr, residueMap ψr x = (residueMap ψj x) ^ (r ^ j) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    set y' : Onr := (Fr ^ j).symm y with hy'
    have hyy : (Fr ^ j) y' = y := by rw [hy', AlgEquiv.apply_symm_apply]
    have hψjy : ψj y = ψr y' := by
      show (ψ.comp ((Fr ^ (-(j : ℤ)) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)) y = (ψ : Onr →+* B) y'
      rw [zpow_neg, zpow_natCast, AlgEquiv.aut_inv]
      rfl
    rw [residueMap, residueMap, Ideal.quotientMap_mk, Ideal.quotientMap_mk, hψjy, ← map_pow, ← map_pow]
    apply (Ideal.Quotient.eq).mpr
    rw [← map_sub]
    apply hψπ
    apply (Ideal.Quotient.eq).mp
    rw [← hyy, hqk, map_pow]
  have hrr0 : ((r : ℕ) : B ⧸ pIdeal r B) = 0 := by
    rw [← map_natCast mkr, hmkr, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hfrobOD : FormalODModule.IsODHom (Φ.map (residueMap ψj)) (Φ.map (residueMap ψr)) frob :=
    CerednikDrinfeld.FormalODModule.isODHom_frobSeries_map_of_forall_eq_pow (residueMap ψj) (residueMap ψr) j hrr0 hg Φ
  have hβOD : FormalODModule.IsODHom (Φ.map (residueMap ψr)) (X₀.map ((residueMap ψr).comp κ)) β₀ψ := by
    rw [← FormalODModule.map_map]
    exact hβ₀.1.map _
  have hγOD := hβOD.comp hfrobOD
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff ((β₀ψ.comp frob) i) = 0 := hγOD.constantCoeff

  have hκσ'OD : FormalODModule.IsODHom (X₀.map ((residueMap ψr).comp κ)) (t.X.map mkr) (Series.map κB σ') := by
    have h := hOD.map κB
    rw [FormalODModule.map_map, FormalODModule.map_map, hκBψ, hκB] at h
    exact h
  have hρ'OD := hκσ'OD.comp hγOD
  have hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0 := hOD.constantCoeff
  have hκσ'0 : ∀ i, MvPowerSeries.constantCoeff ((Series.map κB σ') i) = 0 := hκσ'OD.constantCoeff
  have hκσ0 : ∀ i, MvPowerSeries.constantCoeff ((Series.map κB σ) i) = 0 := by
    intro i
    have h := hρ0 i
    rw [htρ] at h
    rwa [Series.comp, constantCoeff_subst_of_constantCoeff_zero _ hγ0] at h
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
    intro i
    apply hκinj
    have h := hκσ0 i
    rwa [Series.map, MvPowerSeries.constantCoeff_map] at h

  have hκact : ∀ c : Zp2 r, Series.map κB ((t.X.map mkπ).act c) = (t.X.map mkr).act c := by
    intro c
    show Series.map κB (Series.map mkπ (t.X.act c)) = Series.map mkr (t.X.act c)
    rw [Series.map_map, hmkπ, hκB]
  have h1 : Series.map κB (((t.X.map mkπ).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp σ') =
      Series.map κB (((t.X.map mkπ).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp σ) := by rw [hid]
  rw [Series.map_comp κB _ _ hσ'0, Series.map_comp κB _ _ hσ0, hκact, hκact] at h1
  have hidR : ((t.X.map mkr).act (((r : ℕ) : Zp2 r) ^ (ϱ.d + j₁))).comp ((Series.map κB σ').comp (β₀ψ.comp frob)) =
      ((t.X.map mkr).act (((r : ℕ) : Zp2 r) ^ (ϱ'.d + i₁))).comp t.ρ := by
    rw [htρ, ← Series.comp_assoc _ _ _ hκσ'0 hγ0, ← Series.comp_assoc _ _ _ hκσ0 hγ0, h1]

  have hact0 : ∀ c : Zp2 r, ∀ i, MvPowerSeries.constantCoeff ((t.X.map mkr).act c i) = 0 :=
    fun c => ((t.X.map mkr).isLawHom_act c).1
  have hXr4 : (t.X.map mkr).HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree (Series.map mkr (t.X.act (r : Zp2 r))) (r ^ 4)
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map mkr _ (t.X.isLawHom_act _).1 hX4
  have hact : ∀ m : ℕ, FormalODModule.HasKernelOfDegree ((t.X.map mkr).act (((r : ℕ) : Zp2 r) ^ m)) (r ^ (4 * m)) :=
    fun m => CerednikDrinfeld.FormalODModule.HasHeight.hasKernelOfDegree_act_pow hXr4 m
  have hdeg2 := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp hρ0 (hact0 _) hρ.2 (hact (ϱ'.d + i₁))
  rw [← hidR] at hdeg2
  have hρ'0 : ∀ i, MvPowerSeries.constantCoeff (((Series.map κB σ').comp (β₀ψ.comp frob)) i) = 0 := hρ'OD.constantCoeff
  have hdvd := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.dvd_of_comp hρ'0 (hact0 _) (hact (ϱ.d + j₁)) hdeg2
  rw [← pow_add, Nat.pow_dvd_pow_iff_le_right hrp.two_le] at hdvd
  refine ⟨t.n + (ϱ'.d + i₁) - (ϱ.d + j₁), by omega, hρ'OD, ?_⟩
  have heq : r ^ (4 * t.n) * r ^ (4 * (ϱ'.d + i₁)) = r ^ (4 * (t.n + (ϱ'.d + i₁) - (ϱ.d + j₁))) * r ^ (4 * (ϱ.d + j₁)) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [heq] at hdeg2
  exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.of_comp_left hρ'0 (hact0 _) (hact (ϱ.d + j₁)) hdeg2

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_isIsogenyOfHeight_comp_of_act_pow_comp_eq_of_isAdmissible_of_nontrivial (solution)

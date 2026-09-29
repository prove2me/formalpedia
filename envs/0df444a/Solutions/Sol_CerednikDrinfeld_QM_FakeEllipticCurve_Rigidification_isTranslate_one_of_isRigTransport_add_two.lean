-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_one_of_isRigTransport_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9d4391ca-0fbe-5402-ab18-1336a0b8d3b0

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eq_of_represents_of_represents_of_constantCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace ShiftTranslateAux

open MvPowerSeries

theorem constantCoeff_subst_of_constantCoeff_zero {S : Type} [CommRing S] (a : Fin 2 → MvPowerSeries (Fin 2) S)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries (Fin 2) S) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  rw [constantCoeff_subst ha]
  rw [finsum_eq_single _ (0 : Fin 2 →₀ ℕ)]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h; push Not at h; exact hd (Finsupp.ext fun s => by simpa using h s)
    rw [Finsupp.prod, map_prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (by rw [map_pow, ha0, zero_pow hs]), smul_zero]

theorem constantCoeff_comp {S : Type} [CommRing S] (ψ φ : CerednikDrinfeld.SpecialFormal.Series S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    constantCoeff ((ψ.comp φ) i) = constantCoeff (ψ i) :=
  constantCoeff_subst_of_constantCoeff_zero φ hφ (ψ i)

theorem constantCoeff_frobSeries {p : ℕ} [Fact p.Prime] (S : Type) [CommRing S] (j : ℕ) (i : Fin 2) :
    constantCoeff (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S j i) = 0 := by
  show constantCoeff ((X i : MvPowerSeries (Fin 2) S) ^ (p ^ j)) = 0
  rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem frobSeries_comp_frobSeries {p : ℕ} [Fact p.Prime] (S : Type) [CommRing S] (j k : ℕ) :
    (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S j).comp (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S k) =
      CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S (j + k) := by
  funext i
  have ha : HasSubst (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S k) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_frobSeries S k)
  show subst _ ((X i : MvPowerSeries (Fin 2) S) ^ (p ^ j)) = (X i : MvPowerSeries (Fin 2) S) ^ (p ^ (j + k))
  rw [subst_pow ha, subst_X ha]
  show ((X i : MvPowerSeries (Fin 2) S) ^ (p ^ k)) ^ (p ^ j) = _
  rw [← pow_mul, ← pow_add, add_comm]

theorem frobSeries_zero {p : ℕ} [Fact p.Prime] (S : Type) [CommRing S] :
    CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S 0 = CerednikDrinfeld.SpecialFormal.Series.id S := by
  funext i
  show (X i : MvPowerSeries (Fin 2) S) ^ (p ^ 0) = X i
  rw [pow_zero, pow_one]

end ShiftTranslateAux

open ShiftTranslateAux in
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

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (j : ℕ) (t : Rigidified r Φ B) (htX : t.X = X) (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (t₂ : Rigidified r Φ B) (ht₂X : t₂.X = X) (ht₂0 : ∀ i, MvPowerSeries.constantCoeff (t₂.ρ i) = 0)
    (htr₂ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ (j + 2) t₂)
    (hn : t₂.n = t.n + 1) :
    Rigidified.IsTranslate (Series.id (Onr ⧸ pIdeal r Onr)) 1 0 ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) t t₂ := by
  classical
  obtain ⟨κB, σ, hκ1, hκ2, hrep, hρ⟩ := htr
  obtain ⟨κB₂, σ₂, hκ1₂, hκ2₂, hrep₂, hρ₂⟩ := htr₂

  have hκeq : κB₂ = κB := Ideal.Quotient.ringHom_ext (hκ1₂.trans hκ1.symm)

  have hrπ : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
    have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.subset_span rfl
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    have : ((r : ℕ) : B) = algebraMap 𝒪 B u * algebraMap 𝒪 B π := by rw [← map_mul, hu, map_natCast]
    rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hκinj : ∀ z, κB z = 0 → z = 0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h1 : Ideal.Quotient.mk (pIdeal r B) y = 0 := by rw [← hz, ← RingHom.comp_apply, hκ1]
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1 ⊢
    exact (Ideal.span_singleton_le_iff_mem _ |>.2 hrπ) h1

  have hβ0 : ∀ i, MvPowerSeries.constantCoeff ((Series.map (residueMap (ψ : Onr →+* B)) β₀) i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hβ₀.1.constantCoeff i, map_zero]
  have hF0 : ∀ (k : ℕ) (i : Fin 2), MvPowerSeries.constantCoeff (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) k i) = 0 :=
    fun k i => constantCoeff_frobSeries _ k i
  have hβF0 : ∀ (k : ℕ) (i : Fin 2), MvPowerSeries.constantCoeff
      (((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) k)) i) = 0 := by
    intro k i; rw [constantCoeff_comp _ _ (hF0 k)]; exact hβ0 i

  have hρ' : t.ρ = (Series.map κB σ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
      (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) := hρ
  have hρ₂' : t₂.ρ = (Series.map κB₂ σ₂).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
      (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) (j + 2))) := hρ₂

  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
    intro i
    apply hκinj
    have := ht0 i
    rw [hρ', constantCoeff_comp _ _ (hβF0 j)] at this
    rwa [show (Series.map κB σ) i = MvPowerSeries.map κB (σ i) from rfl, MvPowerSeries.constantCoeff_map] at this
  have hσ₂0 : ∀ i, MvPowerSeries.constantCoeff (σ₂ i) = 0 := by
    intro i
    rw [hκeq] at hρ₂'
    apply hκinj
    have := ht₂0 i
    rw [hρ₂', constantCoeff_comp _ _ (hβF0 (j + 2))] at this
    rwa [show (Series.map κB σ₂) i = MvPowerSeries.map κB (σ₂ i) from rfl, MvPowerSeries.constantCoeff_map] at this

  have hσσ : σ = σ₂ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eq_of_represents_of_represents_of_constantCoeff_eq_zero
      𝒪 π Onr Λ coord A₀ θ₀ B ψ x.1 x.2 X θ hX σ σ₂ hσ0 hσ₂0 hrep hrep₂
  subst hσσ
  rw [hκeq] at hρ₂'

  refine ⟨ht₂X.trans htX.symm, 0, ?_⟩
  rw [hn, show 0 + t.n + 1 = 0 + (t.n + 1) from by ring, frobSeries_zero, Series.comp_id, Series.map_id,
    Series.id_comp _ (hF0 2)]
  congr 1
  rw [hρ₂', hρ', Series.comp_assoc _ _ _ (hβF0 j) (hF0 2), Series.comp_assoc _ _ _ (hF0 j) (hF0 2),
    frobSeries_comp_frobSeries]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_one_of_isRigTransport_add_two (solution)

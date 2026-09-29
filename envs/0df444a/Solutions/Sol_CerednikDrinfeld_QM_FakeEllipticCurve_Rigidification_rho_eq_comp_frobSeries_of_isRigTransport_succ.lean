-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.rho_eq_comp_frobSeries_of_isRigTransport_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/76679b95-8e48-51ce-8ec0-05a4505ade76

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_eq_of_represents_of_represents_of_constantCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_rho_eq_comp_frobSeries_of_isRigTransport_succ

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace P3ShiftOne

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

theorem constantCoeff_gamma_eq_zero {r : ℕ} [Fact r.Prime] {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C')
    (β₀ : Series C) (hβ0 : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0) (j : ℕ) :
    ∀ i, MvPowerSeries.constantCoeff (((Series.map f β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) C') ^ (r ^ j))) i) = 0 := by
  intro i
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ _) = 0
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro l; rw [map_pow, MvPowerSeries.constantCoeff_X]; exact zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
  · intro l; rw [map_pow, MvPowerSeries.constantCoeff_X]; exact zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
  · show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hβ0, map_zero]

theorem constantCoeff_sigma_eq_zero {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
    (hκB : κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B))
    (σ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (γ : Series (B ⧸ pIdeal r B))
    (hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0)
    (h : ∀ i, MvPowerSeries.constantCoeff (((Series.map κB σ).comp γ) i) = 0) :
    ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
  intro j0
  have hγS : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
  have e1 : MvPowerSeries.constantCoeff (((Series.map κB σ).comp γ) j0) = κB (MvPowerSeries.constantCoeff (σ j0)) := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst _ (MvPowerSeries.map κB (σ j0))) = _
    rw [constantCoeff_subst_of_forall hγS hγ0, MvPowerSeries.constantCoeff_map]
    rfl
  have hρ0 := h j0
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

end P3ShiftOne

open P3ShiftOne in
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
    (htr₂ : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ (j + 1) t₂) :
    t₂.ρ = t.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) := by
  obtain ⟨κB, σ, hκB, hκBψ, hσ, htρ⟩ := htr
  obtain ⟨κB₂, σ₂, hκB₂, hκBψ₂, hσ₂, htρ₂⟩ := htr₂

  obtain rfl : κB = κB₂ := Ideal.Quotient.ringHom_ext (hκB.trans hκB₂.symm)

  have hβ00 : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
  have hγ0 := fun k => constantCoeff_gamma_eq_zero (r := r) (residueMap (ψ : Onr →+* B)) β₀ hβ00 k
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 :=
    constantCoeff_sigma_eq_zero hunr κB hκB σ _ (hγ0 j) (fun i => by rw [← htρ]; exact ht0 i)
  have hσ₂0 : ∀ i, MvPowerSeries.constantCoeff (σ₂ i) = 0 :=
    constantCoeff_sigma_eq_zero hunr κB hκB σ₂ _ (hγ0 (j + 1)) (fun i => by rw [← htρ₂]; exact ht₂0 i)

  have hσσ : σ₂ = σ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.eq_of_represents_of_represents_of_constantCoeff_eq_zero
      𝒪 π Onr Λ coord A₀ θ₀ B ψ x.1 x.2 X θ hX σ₂ σ hσ₂0 hσ0 hσ₂ hσ
  rw [htρ₂, htρ, hσσ]

  have hF1 : MvPowerSeries.HasSubst (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) :=
    MvPowerSeries.HasSubst.X_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
  have hXj : MvPowerSeries.HasSubst (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j)) :=
    MvPowerSeries.HasSubst.X_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)
  have hγS : MvPowerSeries.HasSubst ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
      (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hγ0 j)
  funext i
  show MvPowerSeries.subst _ _ = MvPowerSeries.subst _ (MvPowerSeries.subst _ _)
  rw [MvPowerSeries.subst_comp_subst_apply hγS hF1]
  congr 1
  funext s
  show MvPowerSeries.subst _ _ = MvPowerSeries.subst _ (MvPowerSeries.subst _ _)
  rw [MvPowerSeries.subst_comp_subst_apply hXj hF1]
  congr 1
  funext l
  rw [MvPowerSeries.subst_pow hF1, MvPowerSeries.subst_X hF1]
  show (MvPowerSeries.X l) ^ r ^ (j + 1) = (MvPowerSeries.X l ^ r ^ 1) ^ r ^ j
  rw [← pow_mul, pow_one, ← pow_succ']

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_rho_eq_comp_frobSeries_of_isRigTransport_succ
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_rho_eq_comp_frobSeries_of_isRigTransport_succ (solution)

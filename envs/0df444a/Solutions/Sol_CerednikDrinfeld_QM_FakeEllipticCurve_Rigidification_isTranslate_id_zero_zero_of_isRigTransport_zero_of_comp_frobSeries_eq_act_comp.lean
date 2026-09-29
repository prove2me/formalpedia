-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/22fdb9a7-4bf1-5469-93b9-fed896e8ad42

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_rho_eq_comp_frobSeries_of_isRigTransport_succ
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp

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

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (hX : x.1.IsFormalModuleVia coord X θ)
    (t : Rigidified r Φ B) (htX : t.X = X) (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 0 t)
    (t'' : Rigidified r Φ B) (ht''X : t''.X = X) (ht''0 : ∀ i, MvPowerSeries.constantCoeff (t''.ρ i) = 0)
    (htr'' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ 1 t'')
    (t' : Rigidified r Φ B) (ht'X : t'.X = X) (ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0) (hn : t'.n = t.n + 1)
    (hrel : t'.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) = (t''.Xbar.act (r : Zp2 r)).comp t''.ρ)
    (χ : Onr →+* B) :
    Rigidified.IsTranslate (Series.id (Onr ⧸ pIdeal r Onr)) 0 0 χ t t' := by
  have hr0 : r ≠ 0 := (Fact.out : r.Prime).ne_zero
  have hFc : ∀ j i, MvPowerSeries.constantCoeff (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j i) = 0 := by
    intro j i
    show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j)) = 0
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ hr0)]
  have hF0 : ∀ e : ℕ, e = 0 → Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) e = Series.id (B ⧸ pIdeal r B) := by
    rintro e rfl
    funext i
    show (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ 0) = MvPowerSeries.X i
    rw [pow_zero, pow_one]
  have hXb : t''.Xbar = t.Xbar := by
    show t''.X.map _ = t.X.map _
    rw [ht''X, htX]
  have hAc : ∀ a : Zp2 r, ∀ i, MvPowerSeries.constantCoeff (t.Xbar.act a i) = 0 := fun a => (t.Xbar.isLawHom_act a).1

  have hshift : t''.ρ = t.ρ.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) 1) :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.rho_eq_comp_frobSeries_of_isRigTransport_succ
      hrr hrN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr ‹IsIndefiniteRamifiedExactlyAt _ _ r rbar› Λ hΛ hΛℤ coord hcoord A₀ X₀ hX₀ θ₀ hA₀ ι Φ hΦ hΦ4 M hM η hη E₀ hE₀ κ hκ n₀ β₀ hβ₀ B ψ hB x X θ hX 0 t htX ht0 htr t'' ht''X ht''0 htr''

  have key : t'.ρ = (t.Xbar.act (r : Zp2 r)).comp t.ρ := by
    apply CerednikDrinfeld.SpecialFormal.Series.eq_of_comp_frobSeries_eq (p := r) 1
    rw [hrel, hshift, hXb, Series.comp_assoc _ _ _ ht0 (hFc 1)]
  refine ⟨ht'X.trans htX.symm, 0, ?_⟩
  rw [hF0 0 rfl, Series.map_id, Series.comp_id, Series.comp_id, Series.comp_id, key, hn,
    ← Series.comp_assoc _ _ _ (hAc _) ht0, ← FormalODModule.act_mul, ← pow_succ, zero_add, add_zero, zero_add]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp (solution)

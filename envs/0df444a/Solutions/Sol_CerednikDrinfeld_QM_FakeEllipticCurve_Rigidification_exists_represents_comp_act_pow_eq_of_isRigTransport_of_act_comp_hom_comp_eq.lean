-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ef5098c8-9bd2-5ebf-adb2-de512a6be572

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace CancelBetaAux

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

private theorem _root_.CancelBetaAux.constantCoeff_comp {S : Type} [CommRing S] (ψ φ : CerednikDrinfeld.SpecialFormal.Series S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    constantCoeff ((ψ.comp φ) i) = constantCoeff (ψ i) :=
  constantCoeff_subst_of_constantCoeff_zero φ hφ (ψ i)

p2m_export "CancelBetaAux" "constantCoeff_comp"
theorem constantCoeff_frobSeries {p : ℕ} [Fact p.Prime] (S : Type) [CommRing S] (j : ℕ) (i : Fin 2) :
    constantCoeff (CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries (p := p) S j i) = 0 := by
  show constantCoeff ((X i : MvPowerSeries (Fin 2) S) ^ (p ^ j)) = 0
  rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

theorem constantCoeff_map_zero {S S' : Type} [CommRing S] [CommRing S'] (g : S →+* S')
    (φ : CerednikDrinfeld.SpecialFormal.Series S) (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    constantCoeff ((φ.map g) i) = 0 := by
  show constantCoeff (MvPowerSeries.map g (φ i)) = 0
  rw [constantCoeff_map, hφ i, map_zero]

end CancelBetaAux

open CancelBetaAux in
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
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ)
    (X X' : FormalODModule r B)
    (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2) (θ' : RelativeGroupLaw.FormalCoordinates x'.1.f 2)
    (j : ℕ) (t t' : Rigidified r Φ B)
    (ht0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (ht'0 : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t)
    (ht' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x'.2 θ' j t')

    (T₀ : FormalODModule.Hom X X') (m : ℕ)
    (hTρ : (t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
        ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ) =
      (t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp t'.ρ) :
    ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ pIdeal r B))
      (σ σ' : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (N : ℕ),

      κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (pIdeal r B) ∧
      κB.comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) = (residueMap (ψ : Onr →+* B)).comp κ ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ x.2.Ab.A,
              PA ≫ x.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ x.2.gA = (θ₀ B'' s).1 →
                PA ≫ x.2.φ' ≫ x.2.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
          [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
          algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
          algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' =
            (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (FakeEllipticCurve.Rigidification.residueLeg π ψ) →
          ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            ∀ PA : Spec (CommRingCat.of B'') ⟶ x'.2.Ab.A,
              PA ≫ x'.2.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
              PA ≫ x'.2.gA = (θ₀ B'' s).1 →
                PA ≫ x'.2.φ' ≫ x'.2.gb = (θ' B'' (fun i => MvFormalGroup.nilEval m (σ' i) s)).1) ∧

      t.ρ = (σ.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) ∧
      t'.ρ = (σ'.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) ∧

      ((t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
          ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (σ.map κB))).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* B))).act ((r : Zp2 r) ^ N)) =
      ((t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp (σ'.map κB)).comp
        (((X₀.map κ).map (residueMap (ψ : Onr →+* B))).act ((r : Zp2 r) ^ N)) := by
  classical
  obtain ⟨κB, σ, hκ1, hκ2, hrep, hρ⟩ := ht
  obtain ⟨κB', σ', hκ1', hκ2', hrep', hρ'⟩ := ht'
  have hκeq : κB = κB' := Ideal.Quotient.ringHom_ext (hκ1.trans hκ1'.symm)
  subst hκeq

  obtain ⟨N₀, δ₀, E_X, hδOD, -, hβδ, -, -⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal
      π hOnr_max hunr K₀ Φ hΦ4 X₀ κ hκ n₀ β₀ hβ₀ E₀ hE₀.1

  have hρF : t.ρ = (σ.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp
      (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) := hρ
  have hρ'F : t'.ρ = (σ'.map κB).comp ((β₀.map (residueMap (ψ : Onr →+* B))).comp
      (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) := hρ'

  have cβ : ∀ i, MvPowerSeries.constantCoeff ((β₀.map (residueMap (p := r) (ψ : Onr →+* B))) i) = 0 :=
    constantCoeff_map_zero _ β₀ hβ₀.1.constantCoeff
  have cδ : ∀ i, MvPowerSeries.constantCoeff ((δ₀.map (residueMap (p := r) (ψ : Onr →+* B))) i) = 0 :=
    constantCoeff_map_zero _ δ₀ hδOD.constantCoeff
  have cF : ∀ i, MvPowerSeries.constantCoeff (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j i) = 0 :=
    constantCoeff_frobSeries _ j
  have cβF : ∀ i, MvPowerSeries.constantCoeff (((β₀.map (residueMap (p := r) (ψ : Onr →+* B))).comp
      (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) i) = 0 :=
    Series.constantCoeff_comp cβ cF
  have cT : ∀ i, MvPowerSeries.constantCoeff ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))) i) = 0 :=
    constantCoeff_map_zero _ _ T₀.isODHom.constantCoeff
  have cσ : ∀ i, MvPowerSeries.constantCoeff ((σ.map κB) i) = 0 := by
    intro i
    have h := ht0 i
    rw [hρF, constantCoeff_comp _ _ cβF] at h
    exact h
  have cσ' : ∀ i, MvPowerSeries.constantCoeff ((σ'.map κB) i) = 0 := by
    intro i
    have h := ht'0 i
    rw [hρ'F, constantCoeff_comp _ _ cβF] at h
    exact h
  have cTσ : ∀ i, MvPowerSeries.constantCoeff (((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (σ.map κB)) i) = 0 :=
    Series.constantCoeff_comp cT cσ

  have hβδ' : (β₀.map (residueMap (p := r) (ψ : Onr →+* B))).comp (δ₀.map (residueMap (p := r) (ψ : Onr →+* B))) =
      ((X₀.map κ).map (residueMap (ψ : Onr →+* B))).act ((r : Zp2 r) ^ N₀) := by
    rw [← Series.map_comp _ _ _ hδOD.constantCoeff, hβδ]
    rfl

  have H1 : (((t'.Xbar.act ((r : Zp2 r) ^ (m + t'.n))).comp
        ((T₀.toSeries.map (Ideal.Quotient.mk (pIdeal r B))).comp (σ.map κB))).comp
          (β₀.map (residueMap (p := r) (ψ : Onr →+* B)))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j) =
      (((t'.Xbar.act ((r : Zp2 r) ^ (m + t.n))).comp (σ'.map κB)).comp
          (β₀.map (residueMap (p := r) (ψ : Onr →+* B)))).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j) := by
    have h := hTρ
    rw [hρF, hρ'F] at h
    rw [Series.comp_assoc _ _ _ cβ cF, Series.comp_assoc _ _ _ cTσ cβF, Series.comp_assoc _ _ _ cσ cβF,
      Series.comp_assoc _ _ _ cβ cF, Series.comp_assoc _ _ _ cσ' cβF]
    exact h

  have H2 := CerednikDrinfeld.SpecialFormal.Series.eq_of_comp_frobSeries_eq (p := r) j _ _ H1

  have H3 := congrArg (fun G => Series.comp G (δ₀.map (residueMap (p := r) (ψ : Onr →+* B)))) H2
  rw [Series.comp_assoc _ _ _ cβ cδ, Series.comp_assoc _ _ _ cβ cδ, hβδ'] at H3
  exact ⟨κB, σ, σ', N₀, hκ1, hκ2, hrep, hrep', hρF, hρ'F, H3⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq (solution)

-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/807fe023-9541-5bc8-99eb-834f5e563bc0

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

namespace CL9

theorem constantCoeff_subst_eq {σ τ : Type} [Fintype σ] {R : Type} [CommRing R]
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
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

theorem constantCoeff_comp_eq {R : Type} [CommRing R] (ψ φ : Series R) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff ((ψ.comp φ) i) = MvPowerSeries.constantCoeff (ψ i) :=
  constantCoeff_subst_eq φ hφ (ψ i)

end CL9

open CL9 in
theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ β₀' : Series (Onr ⧸ pIdeal r Onr)) (N₀ : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N₀))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hπB : Ideal.span {algebraMap 𝒪 B π} = pIdeal r B)
    (E : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E)

    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ' θ j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (u : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (hcmp : FakeEllipticCurve.Rigidification.IsComparison ρ ρ' u uA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (ea ec : ℕ)
    (hcurve : ρ'.φ' ≫ u ≫ ρ.Eb.act ⟨(((r ^ ea : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      uA ≫ f'b ≫ ρ.φ' ≫ ρ.Eb.act ⟨(((r ^ ec : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s))
    (e' : Series (Onr ⧸ pIdeal r Onr)) (he' : e' = β₀'.comp ((Series.map κ ε'.toPowerSeries).comp β₀))

    (hχ : ∀ x : Onr ⧸ pIdeal r Onr,
      residueMap (ψ : Onr →+* B) x = (residueMap ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) x) ^ (r ^ j))

    (k m' : ℕ) (hk : t.n + k + ec = t'.n + N₀ + ea) (hm : j' + m' = j + 2 * k) :
    Rigidified.IsTranslate e' k m' ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) t t'  := by
  classical
  obtain ⟨κB, σ, hκB₁, hκB₂, hσ, ht⟩ := htr
  obtain ⟨κB', σ', hκB₁', hκB₂', hσ', ht'⟩ := htr'

  have hκ : κB' = κB := Ideal.Quotient.ringHom_ext (hκB₁'.trans hκB₁.symm)
  rw [hκ] at ht'
  clear hκB₁' hκB₂' hκ

  have hκinj : Function.Injective κB := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : κB (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk (pIdeal r B) x := congrArg (fun f => f x) hκB₁
    have hy : κB (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (pIdeal r B) y := congrArg (fun f => f y) hκB₁
    rw [hx, hy, Ideal.Quotient.eq, ← hπB] at hxy
    exact (Ideal.Quotient.eq).mpr hxy

  have cβ : ∀ i, MvPowerSeries.constantCoeff ((Series.map (residueMap (ψ : Onr →+* B)) β₀) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hβ₀.constantCoeff i, map_zero]
  have cF : ∀ (j : ℕ) i, MvPowerSeries.constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j)) i) = 0 := by
    intro j i
    show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ j)) = 0
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : r.Prime).ne_zero)]
  have hcc : ∀ (τ : Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})) (jj : ℕ) (tt : Rigidified r Φ B),
      (∀ i, MvPowerSeries.constantCoeff (tt.ρ i) = 0) →
      tt.ρ = (Series.map κB τ).comp ((Series.map (residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ jj))) →
      ∀ i, MvPowerSeries.constantCoeff (τ i) = 0 := by
    intro τ jj tt hρ hrep i
    have h1 := hρ i
    rw [hrep, constantCoeff_comp_eq _ _ (Series.constantCoeff_comp cβ (cF jj)) i] at h1
    have h2 : κB (MvPowerSeries.constantCoeff (τ i)) = 0 := by
      rw [← MvPowerSeries.constantCoeff_map]; exact h1
    exact hκinj (by rw [h2, map_zero])
  have hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := hcc σ j t hadm.constantCoeff_ρ ht
  have hσ'0 : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0 := hcc σ' j' t' hadm'.constantCoeff_ρ ht'

  have hσσ' := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.comp_nthSeries_eq_comp_comp_of_forall_nilEval_of_comp_act_comp_eq_of_constantCoeff_eq_zero π hΛℤ coord hcoord A₀ X₀ θ₀ ψ E X θ hE ρ ρ' σ σ' hσ0 hσ'0
    hσ hσ' u uA hcmp f' hf' f'b hf'b hf'bf ea ec hcurve ε' hε'

  have hσN := CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.nthSeries_comp_eq_comp_nthSeries_of_forall_nilEval π hΛℤ coord hcoord A₀ X₀ θ₀ hA₀ ψ E X θ hE ρ σ hσ0 hσ (r ^ N₀)

  have cκε : ∀ i, MvPowerSeries.constantCoeff ((Series.map κ ε'.toPowerSeries) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.map κ (ε'.toPowerSeries i)) = 0
    rw [MvPowerSeries.constantCoeff_map, ε'.constantCoeff_eq_zero i, map_zero]
  have he'0 : ∀ i, MvPowerSeries.constantCoeff (e' i) = 0 := by
    rw [he']
    exact Series.constantCoeff_comp hβ₀'.constantCoeff (Series.constantCoeff_comp cκε hβ₀.constantCoeff)
  have hfrob := CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow (p := r) (ψ : Onr →+* B)
    ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) j hχ e' he'0

  exact CerednikDrinfeld.SpecialFormal.Rigidified.isTranslate_of_rho_eq_comp_of_comp_nthSeries_eq_of_frob_comm π Φ X₀ κ β₀ β₀' N₀ hβ₀ hβ₀' h₂ ψ
    ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) X t t' htX ht'X κB hκB₁ hκB₂ σ σ' hσ0 hσ'0 j j' ht ht' hσN
    ε'.toPowerSeries ε'.constantCoeff_eq_zero ea ec hσσ' e' he' hfrob k m' hk hm

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isTranslate_of_isRigTransport_of_comp_act_eq_comp_of_germ (solution)

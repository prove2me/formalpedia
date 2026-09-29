-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f2a5340e-7b35-5e3f-865e-991a838357e7

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_rho_eq_comp_and_nthSeries_comp_eq_of_isRigTransport_of_isRigTransport_mapPt
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_le_and_of_comp_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_eq_of_pow_of_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasHeight_hasKernelOfDegree_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_frobSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega NeronModelInfra GoodReductionJacobian

namespace P2mWs44HBPSW

theorem constantCoeff_map_eq_zero {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Series R)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff ((Series.map f φ) i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

end P2mWs44HBPSW

open P2mWs44HBPSW in
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

    {B : Type} [CommRing B] [IsNoetherianRing B] [Nontrivial B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    (hπB : Ideal.span {algebraMap 𝒪 B π} = pIdeal r B) (hBπ : IsNilpotent (algebraMap 𝒪 B π))
    (E Ef : FakeEllipticCurve Λ N B) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hE : E.IsFormalModuleVia coord X θ)
    (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f)
    (hEf : Ef.IsFormalModuleVia coord X (fun B' _ _ s => mapPt q hq (θ B' s)))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef)

    (j : ℕ) (t : Rigidified r Φ B) (hj : j ≤ 1) (htX : t.X = X)
    (htr : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)
    (hadm : t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))
    (j' : ℕ) (t' : Rigidified r Φ B) (hj' : j' ≤ 1) (ht'X : t'.X = X)
    (htr' : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρf (fun B' _ _ s => mapPt q hq (θ B' s)) j' t')
    (hadm' : t'.IsAdmissible ι ((frobTwist Onr Fr (-(j' : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (qb : ρ.Eb.A ⟶ ρf.Eb.A) (hqb : qb ≫ ρf.gb = ρ.gb ≫ q)
    (uA : ρf.Ab.A ⟶ ρ.Ab.A) (huA : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (huAg : uA ≫ ρ.gA = ρf.gA)
    (f' : A₀.A ⟶ A₀.A) (hf' : f' ≫ A₀.f = A₀.f)
    (f'b : ρ.Ab.A ⟶ ρ.Ab.A) (hf'b : f'b ≫ ρ.gA = ρ.gA ≫ f') (hf'bf : f'b ≫ ρ.Ab.f = ρ.Ab.f)
    (n n' : ℕ)
    (hcurve : uA ≫ f'b ≫ ρ.φ' ≫ qb ≫ ρf.Eb.act ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩ =
      ρf.φ' ≫ ρf.Eb.act ⟨(((n' : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (u v α β : ℕ) (hn : n = u * r ^ α) (hn' : n' = u * v * r ^ β)
    (hu : IsUnit ((u : ℕ) : Zp2 r)) (hv : IsUnit ((v : ℕ) : Zp2 r))

    (ε' : MvFormalGroup.End X₀.F)
    (hε' : ∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
      J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
        θ₀ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s) = mapPt f' hf' (θ₀ B' s))
    (e'' : Series (Onr ⧸ pIdeal r Onr))
    (he'' : e'' = β₀'.comp ((Series.map κ (Series.comp ε'.toPowerSeries (X₀.act ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r)))).comp β₀))

    (m' : ℕ) (hker : FormalODModule.HasKernelOfDegree (Series.map (residueMap (ψ : Onr →+* B)) e'') (r ^ (2 * m'))) :
    ∃ k : ℕ, j' + m' = j + 2 * k ∧ t.n + k + α = t'.n + N₀ + β := by
  classical
  have hrp : r.Prime := Fact.out
  subst hn hn'
  subst htX

  haveI hBr : Nontrivial (B ⧸ pIdeal r B) := by
    refine Ideal.Quotient.nontrivial_iff.mpr (fun htop => ?_)
    rw [← hπB, Ideal.span_singleton_eq_top] at htop
    obtain ⟨n, hn⟩ := hBπ
    have := htop.pow n
    rw [hn, isUnit_zero_iff] at this
    exact zero_ne_one this

  obtain ⟨κB, σ, σf, hκB₁, hκB₂, hσ0, hσf0, ht, ht', hlinσ, hlinσf, hσσf⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_rho_eq_comp_and_nthSeries_comp_eq_of_isRigTransport_of_isRigTransport_mapPt
      π hΛℤ coord hcoord A₀ X₀ θ₀ hA₀ ι Φ κ β₀ hβ₀.constantCoeff ψ hπB E Ef t.X θ hE q hq hEf ρ ρf
      j t htr hadm.constantCoeff_ρ j' t' htr' hadm'.constantCoeff_ρ qb hqb uA huA huAg f' hf' f'b hf'b hf'bf
      (u * r ^ α) (u * v * r ^ β) hcurve ε' hε'

  set E2 : Series (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) :=
    Series.comp ε'.toPowerSeries (X₀.act ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r)) with hE2
  have hact0 : ∀ i, MvPowerSeries.constantCoeff (X₀.act ((hv.unit⁻¹ : (Zp2 r)ˣ) : Zp2 r) i) = 0 :=
    (X₀.isLawHom_act _).1
  have hε'map0 : ∀ i, MvPowerSeries.constantCoeff
      ((Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries) i) = 0 :=
    constantCoeff_map_eq_zero _ _ ε'.constantCoeff_eq_zero
  have hUR :=
    CerednikDrinfeld.FormalODModule.nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
      t.X X₀ (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (FakeEllipticCurve.Rigidification.residueLeg π ψ)
      σ σf (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) ε'.toPowerSeries)
      hσ0 hσf0 hε'map0 hlinσf u v α β hu hv hσσf

  have hσσT : (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (t.X.F.nthSeries (r ^ β))).comp σf =
      (Series.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (t.X.F.nthSeries (r ^ α))).comp
        (σ.comp (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) E2)) := by
    rw [hE2, Series.map_comp _ _ _ hact0]
    exact hUR.symm
  have hσN := hlinσ (r ^ N₀)
  have cFrob : ∀ (jj : ℕ) i, MvPowerSeries.constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ jj)) i) = 0 := by
    intro jj i
    show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ jj)) = 0
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_ne_zero _ hrp.ne_zero)]

  set mkπ : B →+* B ⧸ Ideal.span {algebraMap 𝒪 B π} := Ideal.Quotient.mk _ with hmkπ
  set mkr : B →+* B ⧸ pIdeal r B := Ideal.Quotient.mk _ with hmkr
  set ψr : (Onr ⧸ pIdeal r Onr) →+* B ⧸ pIdeal r B := residueMap (ψ : Onr →+* B) with hψr
  set Xr : FormalODModule r (B ⧸ pIdeal r B) := t.X.map mkr with hXr
  set A : ℕ → Series (B ⧸ pIdeal r B) := fun m => Xr.act ((r : Zp2 r) ^ m) with hA
  set S : Series (B ⧸ pIdeal r B) := Series.map κB σ with hS
  set S' : Series (B ⧸ pIdeal r B) := Series.map κB σf with hS'
  set βb : Series (B ⧸ pIdeal r B) := Series.map ψr β₀ with hβb
  set βb' : Series (B ⧸ pIdeal r B) := Series.map ψr β₀' with hβb'
  set Eb : Series (B ⧸ pIdeal r B) := Series.map (ψr.comp κ) E2 with hEb
  set eb : Series (B ⧸ pIdeal r B) := Series.map ψr e'' with heb

  have cA : ∀ m i, MvPowerSeries.constantCoeff (A m i) = 0 := fun m => (Xr.isLawHom_act _).1
  have cS : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := constantCoeff_map_eq_zero _ _ hσ0
  have cS' : ∀ i, MvPowerSeries.constantCoeff (S' i) = 0 := constantCoeff_map_eq_zero _ _ hσf0
  have cβb : ∀ i, MvPowerSeries.constantCoeff (βb i) = 0 := constantCoeff_map_eq_zero _ _ hβ₀.constantCoeff
  have cβb' : ∀ i, MvPowerSeries.constantCoeff (βb' i) = 0 := constantCoeff_map_eq_zero _ _ hβ₀'.constantCoeff
  have cε : ∀ i, MvPowerSeries.constantCoeff (E2 i) = 0 := Series.constantCoeff_comp ε'.constantCoeff_eq_zero ((X₀.isLawHom_act _).1)
  have cEb : ∀ i, MvPowerSeries.constantCoeff (Eb i) = 0 := constantCoeff_map_eq_zero _ _ cε
  have cκε : ∀ i, MvPowerSeries.constantCoeff ((Series.map κ E2) i) = 0 := constantCoeff_map_eq_zero _ _ cε
  have ce' : ∀ i, MvPowerSeries.constantCoeff (e'' i) = 0 := by
    rw [he'']; exact Series.constantCoeff_comp hβ₀'.constantCoeff (Series.constantCoeff_comp cκε hβ₀.constantCoeff)
  have ceb : ∀ i, MvPowerSeries.constantCoeff (eb i) = 0 := constantCoeff_map_eq_zero _ _ ce'
  have cF : ∀ i, MvPowerSeries.constantCoeff ((Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j) i) = 0 := cFrob j
  have cF' : ∀ i, MvPowerSeries.constantCoeff ((Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j') i) = 0 := cFrob j'
  have cX₀ns : ∀ (n : ℕ) i, MvPowerSeries.constantCoeff (X₀.F.nthSeries n i) = 0 := fun n => by
    rw [← X₀.act_natCast]; exact (X₀.isLawHom_act _).1

  have hAns : ∀ m : ℕ, Series.map κB (Series.map mkπ (t.X.F.nthSeries (r ^ m))) = A m := by
    intro m
    show Series.map κB (Series.map mkπ (t.X.F.nthSeries (r ^ m))) = (t.X.map mkr).act ((r : Zp2 r) ^ m)
    rw [Series.map_map, hmkπ, hκB₁, ← t.X.act_natCast, Nat.cast_pow, hmkr]
    rfl

  have hββ' : Series.map κB (Series.map (FakeEllipticCurve.Rigidification.residueLeg π ψ) (X₀.F.nthSeries (r ^ N₀))) =
      βb.comp βb' := by
    rw [Series.map_map, hκB₂, ← Series.map_map, ← X₀.act_natCast, Nat.cast_pow,
      ← FormalODModule.map_act, ← h₂, Series.map_comp _ _ _ hβ₀'.constantCoeff]

  have hI : (A β).comp S' = (A α).comp (S.comp Eb) := by
    have h := congrArg (Series.map κB) hσσT
    rw [Series.map_comp κB _ _ hσf0, Series.map_comp κB _ _ (Series.constantCoeff_comp hσ0 (constantCoeff_map_eq_zero _ _ cε)),
      Series.map_comp κB _ _ (constantCoeff_map_eq_zero _ _ cε), hAns, hAns, Series.map_map, hκB₂] at h
    exact h

  have hII : (A N₀).comp S = S.comp (βb.comp βb') := by
    have h := congrArg (Series.map κB) hσN
    rw [Series.map_comp κB _ _ hσ0, Series.map_comp κB _ _ (constantCoeff_map_eq_zero _ _ (cX₀ns _)),
      hAns, hββ'] at h
    exact h

  have hebEq : eb = βb'.comp (Eb.comp βb) := by
    rw [heb, he'', Series.map_comp _ _ _ (Series.constantCoeff_comp cκε hβ₀.constantCoeff),
      Series.map_comp _ _ _ hβ₀.constantCoeff, Series.map_map]

  have hρt : t.ρ = (S.comp βb).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j) := by
    rw [ht, Series.comp_assoc _ _ _ cβb cF]
  have hρt' : t'.ρ = S'.comp (βb.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j')) := ht'

  have hAadd : ∀ m₁ m₂ : ℕ, A (m₁ + m₂) = (A m₁).comp (A m₂) := fun m₁ m₂ => Xr.act_pow_add m₁ m₂

  have hZ : (A (N₀ + β)).comp t'.ρ = (A α).comp ((S.comp βb).comp (eb.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j'))) := by
    rw [hρt', hAadd, Series.comp_assoc _ _ _ (cA _) (Series.constantCoeff_comp cS' (Series.constantCoeff_comp cβb cF')),
      ← Series.comp_assoc _ _ _ cS' (Series.constantCoeff_comp cβb cF'), hI,
      Series.comp_assoc _ _ _ (Series.constantCoeff_comp cS cEb) (Series.constantCoeff_comp cβb cF'),
      ← Series.comp_assoc (A N₀) (A α) _ (cA _) (Series.constantCoeff_comp (Series.constantCoeff_comp cS cEb) (Series.constantCoeff_comp cβb cF')),
      ← hAadd, add_comm N₀ α, hAadd,
      Series.comp_assoc _ _ _ (cA _) (Series.constantCoeff_comp (Series.constantCoeff_comp cS cEb) (Series.constantCoeff_comp cβb cF')),
      Series.comp_assoc S Eb _ cEb (Series.constantCoeff_comp cβb cF'),
      ← Series.comp_assoc (A N₀) S _ cS (Series.constantCoeff_comp cEb (Series.constantCoeff_comp cβb cF')), hII,
      Series.comp_assoc S (βb.comp βb') _ (Series.constantCoeff_comp cβb cβb') (Series.constantCoeff_comp cEb (Series.constantCoeff_comp cβb cF')),
      Series.comp_assoc βb βb' _ cβb' (Series.constantCoeff_comp cEb (Series.constantCoeff_comp cβb cF')),
      hebEq,
      Series.comp_assoc S βb _ cβb (Series.constantCoeff_comp (Series.constantCoeff_comp cβb' (Series.constantCoeff_comp cEb cβb)) cF'),
      Series.comp_assoc βb' (Eb.comp βb) _ (Series.constantCoeff_comp cEb cβb) cF',
      Series.comp_assoc Eb βb _ cβb cF']

  obtain ⟨-, hX4, hρ⟩ := hadm
  obtain ⟨-, -, hρ'⟩ := hadm'
  have cρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := hρ.1.constantCoeff
  have cρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0 := hρ'.1.constantCoeff
  have hXr4 : Xr.HasHeight 4 := by
    show FormalODModule.HasKernelOfDegree (Series.map mkr (t.X.act (r : Zp2 r))) (r ^ 4)
    exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map mkr _ (t.X.isLawHom_act _).1 hX4
  have dA : ∀ m : ℕ, FormalODModule.HasKernelOfDegree (A m) (r ^ (4 * m)) :=
    fun m => CerednikDrinfeld.FormalODModule.HasHeight.hasKernelOfDegree_act_pow hXr4 m
  have dF : FormalODModule.HasKernelOfDegree (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j) (r ^ (2 * j)) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_frobSeries (r := r) (B ⧸ pIdeal r B) j
  have dF' : FormalODModule.HasKernelOfDegree (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j') (r ^ (2 * j')) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_frobSeries (r := r) (B ⧸ pIdeal r B) j'

  have hρdeg : FormalODModule.HasKernelOfDegree ((S.comp βb).comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j)) (r ^ (4 * t.n)) := by rw [← hρt]; exact hρ.2
  obtain ⟨hjle, dSβ⟩ := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.le_and_of_comp_pow cF (Series.constantCoeff_comp cS cβb) dF hρdeg

  have dL : FormalODModule.HasKernelOfDegree ((A (N₀ + β)).comp t'.ρ) (r ^ (4 * t'.n) * r ^ (4 * (N₀ + β))) :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp cρ' (cA _) hρ'.2 (dA _)

  have dR : FormalODModule.HasKernelOfDegree ((A α).comp ((S.comp βb).comp (eb.comp (Rigidified.frobSeries (p := r) (B ⧸ pIdeal r B) j'))))
      (r ^ (2 * j') * r ^ (2 * m') * r ^ (4 * t.n - 2 * j) * r ^ (4 * α)) :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp
      (Series.constantCoeff_comp (Series.constantCoeff_comp cS cβb) (Series.constantCoeff_comp ceb cF')) (cA _)
      (CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp (Series.constantCoeff_comp ceb cF') (Series.constantCoeff_comp cS cβb)
        (CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp cF' ceb dF' hker) dSβ) (dA _)
  rw [← hZ, ← pow_add, ← pow_add, ← pow_add] at dR
  rw [← pow_add] at dL
  have hexp := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.eq_of_pow_of_pow dL dR

  refine ⟨t'.n + N₀ + β - t.n - α, ?_, ?_⟩ <;> omega

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit (solution)

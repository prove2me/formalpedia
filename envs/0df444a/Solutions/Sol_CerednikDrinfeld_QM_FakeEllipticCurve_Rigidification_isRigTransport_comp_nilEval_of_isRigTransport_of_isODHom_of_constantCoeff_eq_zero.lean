-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e8e7d492-723e-5934-8f37-4afe3bf41835

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion

namespace TCCdd

open MvPowerSeries in

theorem nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] {R R' B'' : Type} [CommRing R] [CommRing R'] [CommRing B'']
    [Algebra R B''] [Algebra R' B''] (f : R →+* R') (h : algebraMap R B'' = (algebraMap R' B'').comp f)
    (n : ℕ) (φ : MvPowerSeries σ R) (a : σ → B'') :
    MvFormalGroup.nilEval n (MvPowerSeries.map f φ) a = MvFormalGroup.nilEval n φ a := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← h]

open MvPowerSeries in

theorem constantCoeff_subst_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {R : Type} [CommRing R]
    {a : σ → MvPowerSeries τ R} (ha' : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (subst a f) = MvPowerSeries.constantCoeff f := by
  have ha := hasSubst_of_constantCoeff_zero ha'
  rw [constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have : constantCoeff (d.prod fun s e ↦ a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : ∃ i : σ, d i ≠ 0 := by
        by_contra! hc
        exact hd <| Finsupp.ext hc
      simp [map_finsuppProd, ha']
      exact Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this, smul_zero]

end TCCdd

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (β₀ : Series (Onr ⧸ pIdeal r Onr))

    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B)
    {E : FakeEllipticCurve Λ N B} (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (j : ℕ)
    {Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)} (t : Rigidified r Φ B)
    (ht : FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ j t)

    (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (hβ₀c : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0)
    (hρc : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0)

    (Y : FormalODModule r B) (u v : Series B)
    (hu : FormalODModule.IsODHom t.X Y u) (hv : FormalODModule.IsODHom Y t.X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (θ' : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ' : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        θ' B'' s = θ B'' (fun i => MvFormalGroup.nilEval n (v i) s)) :
    FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ ρ θ' j
      ({ X := Y, n := t.n, ρ := (u.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ } : Rigidified r Φ B) :=
  by
  classical
  obtain ⟨κB, σ, hκ1, hκ2, hrep, hρt⟩ := ht
  have hr : r.Prime := Fact.out

  have hFrc : ∀ i, MvPowerSeries.constantCoeff
      ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j)) i) = 0 := by
    intro i
    simp only [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (pow_pos hr.pos j).ne']
  have hinner : ∀ i, MvPowerSeries.constantCoeff
      (((CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j))) i) = 0 := by
    refine CerednikDrinfeld.SpecialFormal.Series.constantCoeff_comp (fun i => ?_) hFrc
    show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (β₀ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hβ₀c, map_zero]
  have hrπ : ((r : ℕ) : B) ∈ Ideal.span {algebraMap 𝒪 B π} := by
    have : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    have := congrArg (algebraMap 𝒪 B) hc
    rw [map_mul, map_natCast] at this
    rw [← this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hκinj : ∀ c, κB c = 0 → c = 0 := by
    intro c hc
    obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
    have h0 : Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal r B) c₀ = 0 := by
      rw [← hc]; exact (congrArg (fun g => g c₀) hκ1).symm
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0 ⊢
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h0
    rw [← he]
    exact Ideal.mul_mem_left _ _ hrπ
  have hσc : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0 := by
    intro i
    apply hκinj
    have h0 := hρc i
    rw [hρt] at h0
    change MvPowerSeries.constantCoeff (MvPowerSeries.subst _ ((CerednikDrinfeld.SpecialFormal.Series.map κB σ) i)) = 0 at h0
    rw [TCCdd.constantCoeff_subst_of_constantCoeff_eq_zero hinner] at h0
    rwa [show (CerednikDrinfeld.SpecialFormal.Series.map κB σ) i = MvPowerSeries.map κB (σ i) from rfl,
      MvPowerSeries.constantCoeff_map] at h0
  have hσκc : ∀ i, MvPowerSeries.constantCoeff ((CerednikDrinfeld.SpecialFormal.Series.map κB σ) i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map κB (σ i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hσc, map_zero]
  have huc : ∀ i, MvPowerSeries.constantCoeff (u i) = 0 := hu.constantCoeff

  refine ⟨κB, (u.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ, hκ1, hκ2, ?_, ?_⟩
  ·
    intro B'' _ instQ instB instO h1 h2 J m hJ s hs PA hPAf hPAg
    rw [hrep B'' h1 h2 J m hJ s hs PA hPAf hPAg]
    have hpJ : ∀ i, MvFormalGroup.nilEval m (σ i) s ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσc (MvPowerSeries.X 0)).1
    have hupJ : ∀ i, MvFormalGroup.nilEval m (u i) (fun l => MvFormalGroup.nilEval m (σ l) s) ∈ J :=
      (MvFormalGroup.nilEval_subst_of_mem J m hJ _ hpJ u huc (MvPowerSeries.X 0)).1
    have e1 : (fun i => MvFormalGroup.nilEval m
          (((u.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π}))).comp σ) i) s) =
        fun i => MvFormalGroup.nilEval m (u i) (fun l => MvFormalGroup.nilEval m (σ l) s) := by
      funext i
      show MvFormalGroup.nilEval m (MvPowerSeries.subst σ
          (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) (u i))) s = _
      rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσc _).2]
      exact TCCdd.nilEval_map _ h1 m (u i) _
    have e3 : ∀ i, MvFormalGroup.nilEval m (MvPowerSeries.X i : MvPowerSeries (Fin 2) B)
        (fun l => MvFormalGroup.nilEval m (σ l) s) = MvFormalGroup.nilEval m (σ i) s := by
      intro i
      rw [← TCCdd.nilEval_map (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) h1 m
          (MvPowerSeries.X i : MvPowerSeries (Fin 2) B), MvPowerSeries.map_X,
        ← (MvFormalGroup.nilEval_subst_of_mem J m hJ s hs σ hσc (MvPowerSeries.X i)).2,
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hσc) i]
    have e2 : θ' B'' (fun i => MvFormalGroup.nilEval m (u i) (fun l => MvFormalGroup.nilEval m (σ l) s)) =
        θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s) := by
      rw [hθ' B'' J m hJ _ hupJ]
      congr 1
      funext i
      rw [← (MvFormalGroup.nilEval_subst_of_mem J m hJ _ hpJ u huc (v i)).2,
        show MvPowerSeries.subst u (v i) = MvPowerSeries.X i from congrFun hvu i]
      exact e3 i
    rw [e1, e2]
  ·
    show (u.map (Ideal.Quotient.mk (pIdeal r B))).comp t.ρ = _
    rw [hρt, CerednikDrinfeld.SpecialFormal.Series.map_comp _ _ _ hσc, CerednikDrinfeld.SpecialFormal.Series.map_map, hκ1,
      CerednikDrinfeld.SpecialFormal.Series.comp_assoc _ _ _ hσκc hinner]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_isRigTransport_comp_nilEval_of_isRigTransport_of_isODHom_of_constantCoeff_eq_zero (solution)

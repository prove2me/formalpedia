-- Prove2me | solution 1 for CerednikDrinfeld.FormalQuotientDatum.exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/cbcfd828-54e0-5ba2-99f1-627506f08e44

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalQuotientDatum_exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace P2mWs2K3

theorem exists_algHom_of_isAlgClosed
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (hmax : (Ideal.span {π}).IsMaximal)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (K : Type) [Field K] [IsAlgClosed K] [Algebra 𝒪 K] (hK : algebraMap 𝒪 K π = 0) :
    Nonempty (Onr →ₐ[𝒪] K) := by
  classical

  let I : Ideal 𝒪 := Ideal.span {π}
  let J : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π}
  letI : I.IsMaximal := hmax
  letI : J.IsMaximal := hOnr_max
  letI fF : Field (𝒪 ⧸ I) := Ideal.Quotient.field I
  letI fL : Field (Onr ⧸ J) := Ideal.Quotient.field J
  have hIJ : I ≤ J.comap (algebraMap 𝒪 Onr) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hIK : ∀ a ∈ I, algebraMap 𝒪 K a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hK, mul_zero]

  let iL : 𝒪 ⧸ I →+* Onr ⧸ J := Ideal.quotientMap J (algebraMap 𝒪 Onr) hIJ
  let iK : 𝒪 ⧸ I →+* K := Ideal.Quotient.lift I (algebraMap 𝒪 K) hIK
  letI aL : Algebra (𝒪 ⧸ I) (Onr ⧸ J) := iL.toAlgebra
  letI aK : Algebra (𝒪 ⧸ I) K := iK.toAlgebra

  haveI : Algebra.IsAlgebraic (𝒪 ⧸ I) (Onr ⧸ J) := by
    refine ⟨fun l => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective l
    obtain ⟨p, hp, hpx⟩ := hOnr_alg x
    refine ⟨p.map (Ideal.Quotient.mk I), (hp.map _).ne_zero, ?_⟩
    have hcomp : (algebraMap (𝒪 ⧸ I) (Onr ⧸ J)).comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp (algebraMap 𝒪 Onr) := by
      ext a; rfl
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpx

  let ψ₀ : (Onr ⧸ J) →ₐ[𝒪 ⧸ I] K := IsAlgClosed.lift
  refine ⟨{ toRingHom := ψ₀.toRingHom.comp (Ideal.Quotient.mk J), commutes' := fun a => ?_ }⟩
  show ψ₀ (Ideal.Quotient.mk J (algebraMap 𝒪 Onr a)) = algebraMap 𝒪 K a
  have h1 : Ideal.Quotient.mk J (algebraMap 𝒪 Onr a) = algebraMap (𝒪 ⧸ I) (Onr ⧸ J) (Ideal.Quotient.mk I a) := rfl
  rw [h1, AlgHom.commutes]
  show iK (Ideal.Quotient.mk I a) = algebraMap 𝒪 K a
  rw [Ideal.Quotient.lift_mk]

end P2mWs2K3

open P2mWs2K3 in
theorem solution

    {r : ℕ} [Fact r.Prime]
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
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)
    :
    ∃ v : ∀ n : ℕ, D.Y n ⟶ Limits.pullback f (sR n),

      (∀ n : ℕ, v n ≫ Limits.pullback.snd f (sR n) = D.yb n) ∧

      (∀ n : ℕ, IsPullback (D.yt n) (v n) (v (n + 1)) (xn n)) ∧

      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        D.q n B hB x ≫ v n ≫ Limits.pullback.fst f (sR n) = (Θ B ⟨n + 1, hB⟩ x).1) ∧

      (∀ (n : ℕ) (K : Type) [Field K] [IsAlgClosed K] (y y' : Spec (CommRingCat.of K) ⟶ D.Y n),
        y ≫ v n = y' ≫ v n → y = y') := by
  classical

  obtain ⟨u, hu_over, hu_yt, hu_q, -⟩ := D.univ 𝒳 f Θ hΘnat hΘinv

  have htR' : ∀ n : ℕ, tR n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))) := by
    intro n
    haveI : IsClosedImmersion (sR (n + 1)) := by
      rw [hsR]
      exact IsClosedImmersion.spec_of_surjective _ (fun b => Ideal.Quotient.mk_surjective b)
    rw [← cancel_mono (sR (n + 1)), htR, hsR, hsR, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : ∀ n : ℕ, u n ≫ f = D.yb n ≫ sR n := by intro n; rw [hu_over, hsR]
  refine ⟨fun n => pullback.lift (u n) (D.yb n) (hw n), fun n => pullback.lift_snd _ _ _, ?_, ?_, ?_⟩

  · intro n

    have t : IsPullback (xn n) (pullback.snd f (sR n)) (pullback.snd f (sR (n + 1))) (tR n) := by
      refine IsPullback.of_right ?_ (hxn₂ n) (IsPullback.of_hasPullback f (sR (n + 1)))
      rw [hxn₁, htR]
      exact IsPullback.of_hasPullback f (sR n)

    have s : IsPullback (D.yt n) (pullback.lift (u n) (D.yb n) (hw n) ≫ pullback.snd f (sR n))
        (pullback.lift (u (n + 1)) (D.yb (n + 1)) (hw (n + 1)) ≫ pullback.snd f (sR (n + 1))) (tR n) := by
      rw [pullback.lift_snd, pullback.lift_snd, htR']
      exact D.yt_isPullback n
    have p : D.yt n ≫ pullback.lift (u (n + 1)) (D.yb (n + 1)) (hw (n + 1)) =
        pullback.lift (u n) (D.yb n) (hw n) ≫ xn n := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, hxn₁, pullback.lift_fst, hu_yt]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, hxn₂, ← Category.assoc, pullback.lift_snd,
          (D.yt_isPullback n).w, htR']
    exact IsPullback.of_bot s p t

  · intro n B _ _ hB x
    rw [pullback.lift_fst, hu_q]

  · intro n K _ _ y y' hyy

    have hb : y ≫ D.yb n = y' ≫ D.yb n := by
      have := congrArg (fun z => z ≫ pullback.snd f (sR n)) hyy
      simpa only [Category.assoc, pullback.lift_snd] using this
    let φ : CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) ⟶ CommRingCat.of K := Spec.preimage (y ≫ D.yb n)
    have hφ : Spec.map φ = y ≫ D.yb n := Spec.map_preimage _
    letI alg : Algebra 𝒪 K := (φ.hom.comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).toAlgebra
    have halg : algebraMap 𝒪 K = φ.hom.comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) := rfl
    have hover : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K)) =
        (y ≫ D.yb n) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) := by
      rw [halg, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hφ]
    have hKn : (algebraMap 𝒪 K π) ^ (n + 1) = 0 := by
      rw [← map_pow, halg, RingHom.comp_apply, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]
    have hK0 : algebraMap 𝒪 K π = 0 := pow_eq_zero_iff (n := n + 1) (Nat.succ_ne_zero n) |>.mp hKn

    haveI : (Ideal.span {π}).IsMaximal := by
      letI := hdvr
      rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal 𝒪
    obtain ⟨ψ⟩ := exists_algHom_of_isAlgClosed π this Onr hOnr_max hOnr_alg K hK0

    have hy_over : y ≫ D.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K)) := by rw [hover, Category.assoc]
    have hy'_over : y' ≫ D.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K)) := by rw [hover, Category.assoc, ← Category.assoc, ← hb, Category.assoc]
    obtain ⟨P, hP⟩ := (D.q_fib n K hKn ψ).1 y hy_over
    obtain ⟨P', hP'⟩ := (D.q_fib n K hKn ψ).1 y' hy'_over
    rw [← hP, ← hP']
    apply ((D.q_fib n K hKn ψ).2 P P').mpr
    apply ((hΘfib K ⟨n + 1, hKn⟩ ψ).2 P P').mp
    apply Subtype.ext
    rw [← hu_q n K hKn (ψ, P), ← hu_q n K hKn (ψ, P'), hP, hP', ← pullback.lift_fst (u n) (D.yb n) (hw n),
      ← Category.assoc, ← Category.assoc, hyy]

end S_CerednikDrinfeld_FormalQuotientDatum_exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_FormalQuotientDatum_exists_hom_pullback_comp_eq_theta_of_cerednikDrinfeld_quotient (solution)

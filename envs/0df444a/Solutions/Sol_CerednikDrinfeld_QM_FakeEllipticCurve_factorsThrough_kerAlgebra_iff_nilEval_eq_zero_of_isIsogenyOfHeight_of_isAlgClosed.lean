-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/149787a9-2598-5a81-a2ec-bc5d6f15a9c1

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace KSdd

theorem isAdicComplete_of_pow_eq_bot {S : Type} [CommRing S] (J : Ideal S) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) :
    IsAdicComplete J S := by
  have hH : IsHausdorff J S := by
    refine ⟨fun x hx => ?_⟩
    have h := hx (n + 1)
    rw [hJ, Submodule.bot_smul, SModEq.bot] at h
    exact h
  have hP : IsPrecomplete J S := by
    refine ⟨fun {f} hf => ⟨f (n + 1), fun m => ?_⟩⟩
    by_cases hm : m ≤ n + 1
    · exact hf hm
    · have hle : n + 1 ≤ m := by omega
      have h1 : f (n + 1) ≡ f m [SMOD J ^ (n + 1) • (⊤ : Submodule S S)] := hf hle
      rw [hJ, Submodule.bot_smul, SModEq.bot] at h1
      have : J ^ m = ⊥ := by
        apply le_bot_iff.mp
        calc J ^ m ≤ J ^ (n + 1) := Ideal.pow_le_pow_right hle
          _ = ⊥ := hJ
      rw [this, Submodule.bot_smul, SModEq.bot, h1]
  exact (isAdicComplete_iff J S).mpr ⟨hH, hP⟩

theorem exists_algHom_kerAlgebra_of_nilEval_eq_zero {k : Type} [CommRing k]
    (γ : Fin 2 → MvPowerSeries (Fin 2) k)
    (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (s : Fin 2 → B'') (hs : ∀ i, s i ∈ J) (hγ : ∀ i, MvFormalGroup.nilEval n (γ i) s = 0) :
    ∃ φ : FormalODModule.KerAlgebra γ →ₐ[k] B'',
      ∀ i, φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)) = s i := by
  classical
  haveI : IsAdicComplete J B'' := isAdicComplete_of_pow_eq_bot J n hJ
  have hx : ∀ i, s i ∈ J.radical := fun i => Ideal.le_radical (hs i)
  let ψ : MvPowerSeries (Fin 2) k →ₐ[k] B'' := MvFormalGroup.adicEvalAlgHom J hx
  have hψ : ∀ f, ψ f = MvFormalGroup.adicEval J s f := fun f =>
    congrFun (MvFormalGroup.coe_adicEvalAlgHom (R := k) J hx) f
  have hker : ∀ f ∈ Ideal.span (Set.range γ), ψ f = 0 := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i, rfl⟩
      rw [hψ, ← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ (γ i) s hs]
      exact hγ i
    · exact map_zero ψ
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  refine ⟨Ideal.Quotient.liftₐ (Ideal.span (Set.range γ)) ψ hker, fun i => ?_⟩
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  show ψ (MvPowerSeries.X i) = s i
  rw [hψ, MvFormalGroup.adicEval_X]

open MvPowerSeries in

theorem exists_sub_trunc'_eq {k : Type} [CommRing k] (f : MvPowerSeries (Fin 2) k) (n : ℕ) :
    ∃ q₀ q₁ : MvPowerSeries (Fin 2) k,
      f - ((MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => n) f : MvPolynomial (Fin 2) k) :
        MvPowerSeries (Fin 2) k) = X 0 ^ (n + 1) * q₀ + X 1 ^ (n + 1) * q₁ := by
  classical
  set g : MvPowerSeries (Fin 2) k :=
    f - ((MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => n) f : MvPolynomial (Fin 2) k) :
        MvPowerSeries (Fin 2) k) with hg
  have hgc : ∀ e : Fin 2 →₀ ℕ, e 0 ≤ n → e 1 ≤ n → coeff e g = 0 := by
    intro e h0 h1
    have hle : e ≤ Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => n) := by
      intro i; fin_cases i <;> simpa
    simp only [hg, map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]
  let g₀ : MvPowerSeries (Fin 2) k := fun e => if n < e 0 then coeff e g else 0
  have hg₀ : ∀ e, coeff e g₀ = if n < e 0 then coeff e g else 0 := fun e => rfl
  have hd₀ : (X 0 : MvPowerSeries (Fin 2) k) ^ (n + 1) ∣ g₀ := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [hg₀, if_neg (by omega)]
  have hd₁ : (X 1 : MvPowerSeries (Fin 2) k) ^ (n + 1) ∣ g - g₀ := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hg₀]
    by_cases h0 : n < m 0
    · rw [if_pos h0, sub_self]
    · rw [if_neg h0, sub_zero]
      exact hgc m (by omega) (by omega)
  obtain ⟨q₀, hq₀⟩ := hd₀
  obtain ⟨q₁, hq₁⟩ := hd₁
  exact ⟨q₀, q₁, by rw [← hq₀, ← hq₁]; abel⟩

theorem isNilpotent_mk_X {k : Type} [Field k] (γ : Series k)
    (hγc : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0)
    (hfin : Module.Finite k (FormalODModule.KerAlgebra γ)) (hnt : Nontrivial (FormalODModule.KerAlgebra γ)) (i : Fin 2) :
    IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) := by
  classical
  haveI := hfin
  haveI := hnt
  haveI : IsLocalRing (FormalODModule.KerAlgebra γ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span (Set.range γ))) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (FormalODModule.KerAlgebra γ) := IsArtinianRing.of_finite k _

  have hIle : ∀ a ∈ Ideal.span (Set.range γ), MvPowerSeries.constantCoeff a = 0 := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩; exact hγc j
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  let ev0 : FormalODModule.KerAlgebra γ →+* k :=
    Ideal.Quotient.lift (Ideal.span (Set.range γ)) (MvPowerSeries.constantCoeff) hIle
  have hmem : Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ∈
      IsLocalRing.maximalIdeal (FormalODModule.KerAlgebra γ) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ev0
    rw [Ideal.Quotient.lift_mk, MvPowerSeries.constantCoeff_X] at this
    exact not_isUnit_zero this
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := FormalODModule.KerAlgebra γ)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.zero_eq_bot] at hN
  refine ⟨N, ?_⟩
  have := Ideal.pow_mem_pow hmem N
  rwa [hN, Ideal.mem_bot] at this

end KSdd

open KSdd in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    ∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
        (FactorsThrough (θA (FormalODModule.KerAlgebra γ) (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i))).1 (θA B'' s) ↔
          ∀ i, MvFormalGroup.nilEval n (γ i) s = 0) := by
  classical
  intro B'' _ _ J n hJ s hs

  have hγc : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := hγ.1.constantCoeff
  have hnt : Nontrivial (FormalODModule.KerAlgebra γ) := by
    have h1 := hγ.2.2.2 k (RingHom.id k)
    rw [CerednikDrinfeld.SpecialFormal.Series.map_ringHom_id] at h1
    apply Module.nontrivial_of_finrank_pos (R := k)
    rw [h1]; exact pow_pos (Fact.out : r.Prime).pos h
  have hXnil : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)) :=
    isNilpotent_mk_X γ hγc hγ.2.1 hnt
  obtain ⟨hnat, hcoords⟩ := hA.1
  constructor
  ·
    rintro ⟨P₀, hP₀⟩

    obtain ⟨f, rfl⟩ := Spec.map_surjective P₀

    have hfalg : f.hom.comp (algebraMap k (FormalODModule.KerAlgebra γ)) = algebraMap k B'' := by
      have h1 := congrArg (fun g => g ≫ A.f) hP₀
      simp only [Category.assoc] at h1
      rw [(θA _ _).2, (θA B'' s).2, Scheme.specOver, ← Spec.map_comp] at h1
      have h2 := Spec.map_injective h1
      have h3 := congrArg CommRingCat.Hom.hom h2
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h3
    let fa : FormalODModule.KerAlgebra γ →ₐ[k] B'' :=
      { toRingHom := f.hom, commutes' := fun c => congrFun (congrArg DFunLike.coe hfalg) c }

    set s' : Fin 2 → B'' := fun i => f.hom (Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i)) with hs'
    have hs'nil : ∀ i, IsNilpotent (s' i) := fun i => (hXnil i).map f.hom
    have hθeq : θA B'' s' = θA B'' s := by
      have h1 := hnat (FormalODModule.KerAlgebra γ) B'' fa
        (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i)) hXnil
      apply Subtype.ext
      rw [show s' = (fa : FormalODModule.KerAlgebra γ → B'') ∘ (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i)) from rfl,
        h1, GoodReductionJacobian.schemeHomOverComp_coe, ← hP₀]
      rfl

    let J' : Ideal B'' := Ideal.span (Set.range s ∪ Set.range s')
    have hJ'nil : IsNilpotent J' := by
      apply (Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Finset.univ.image s ∪ Finset.univ.image s'), by simp [J']⟩).mpr
      rw [Ideal.span_le]
      rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨n + 1, by have := Ideal.pow_mem_pow (hs i) (n + 1); rwa [hJ, Ideal.mem_bot] at this⟩
      · exact hs'nil i
    obtain ⟨M, hM⟩ := hJ'nil
    have hJ'M : J' ^ (M + 1) = ⊥ := by
      rw [Ideal.zero_eq_bot] at hM
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ M)).trans hM.le)
    have hss' : s = s' := by
      refine (hcoords B'' J' M hJ'M).2.1 s s' (fun i => Ideal.subset_span (Or.inl ⟨i, rfl⟩))
        (fun i => Ideal.subset_span (Or.inr ⟨i, rfl⟩)) hθeq.symm

    intro i
    have hpoly : ∀ q : MvPolynomial (Fin 2) k,
        MvPolynomial.aeval s' q = fa (Ideal.Quotient.mk (Ideal.span (Set.range γ)) (q : MvPowerSeries (Fin 2) k)) := by
      intro q
      have : (MvPolynomial.aeval s' : MvPolynomial (Fin 2) k →ₐ[k] B'') =
          (fa.comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range γ)))).comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
        apply MvPolynomial.algHom_ext
        intro j
        simp [fa, hs', MvPolynomial.coeToMvPowerSeries.algHom_apply]
      exact congrFun (congrArg DFunLike.coe this) q
    obtain ⟨q₀, q₁, hq⟩ := exists_sub_trunc'_eq (γ i) n
    have hγmk : Ideal.Quotient.mk (Ideal.span (Set.range γ)) (γ i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    rw [hss']
    unfold MvFormalGroup.nilEval
    rw [hpoly]
    have e1 : ((MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => n) (γ i) : MvPolynomial (Fin 2) k) :
        MvPowerSeries (Fin 2) k) = γ i - (MvPowerSeries.X 0 ^ (n + 1) * q₀ + MvPowerSeries.X 1 ^ (n + 1) * q₁) := by
      rw [← hq]; abel
    rw [e1, map_sub, hγmk, zero_sub, map_neg, map_add, map_mul, map_mul, map_pow, map_pow, map_add, map_mul,
      map_mul, map_pow, map_pow]
    have hz : ∀ j, (fa (Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X j))) ^ (n + 1) = 0 := by
      intro j
      have : s' j ^ (n + 1) ∈ J ^ (n + 1) := Ideal.pow_mem_pow (by rw [← hss']; exact hs j) (n + 1)
      rwa [hJ, Ideal.mem_bot] at this
    rw [hz, hz, zero_mul, zero_mul, add_zero, neg_zero]
  ·
    intro hγs
    obtain ⟨φ, hφ⟩ := exists_algHom_kerAlgebra_of_nilEval_eq_zero γ B'' J n hJ s hs hγs
    have h1 := hnat (FormalODModule.KerAlgebra γ) B'' φ
      (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i)) hXnil
    have hs_eq : (φ : FormalODModule.KerAlgebra γ → B'') ∘
        (fun i => Ideal.Quotient.mk (Ideal.span (Set.range γ)) (MvPowerSeries.X i)) = s := funext hφ
    rw [hs_eq] at h1
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
    rw [h1, GoodReductionJacobian.schemeHomOverComp_coe]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_kerAlgebra_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed (solution)

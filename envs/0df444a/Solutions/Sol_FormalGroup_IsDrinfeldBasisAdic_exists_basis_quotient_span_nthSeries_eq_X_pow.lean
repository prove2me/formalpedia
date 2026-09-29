-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_basis_quotient_span_nthSeries_eq_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dfdf3e32-153f-5314-b956-1a2594eab294

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow

set_option autoImplicit false

open PowerSeries Polynomial

namespace R4ConvFKR

section AdicMem

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem adic_eval₂_mem (J : Ideal S) [IsAdicComplete J S] {σ : Type*} [Finite σ] {x : σ → S}
    (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R} (hf : MvPowerSeries.constantCoeff f = 0) :
    (letI : UniformSpace R := ⊥
     letI : WithIdeal S := ⟨J⟩
     MvPowerSeries.eval₂ (algebraMap R S) x f) ∈ J := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  show MvPowerSeries.eval₂ (algebraMap R S) x f ∈ J
  have hφ : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (hx s), ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  have hsum := MvPowerSeries.hasSum_eval₂ hφ ha f

  have hnhds : ((J : Ideal S) : Set S) ∈ nhds (0 : S) := by
    have h := (J.hasBasis_nhds_zero_adic).mem_of_mem (i := 1) trivial
    simpa only [pow_one] using h
  have hopen : IsOpen ((J.toAddSubgroup : AddSubgroup S) : Set S) :=
    J.toAddSubgroup.isOpen_of_mem_nhds hnhds
  have hclosed : IsClosed ((J : Ideal S) : Set S) := J.toAddSubgroup.isClosed_of_isOpen hopen
  refine hclosed.mem_of_tendsto hsum (Filter.Eventually.of_forall fun t => ?_)
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    have h0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) f = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hf
    rw [h0, map_zero, zero_mul]
    exact Submodule.zero_mem _
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod]
    refine Ideal.prod_mem _ (Finsupp.mem_support_iff.mpr hs) ?_
    exact Ideal.pow_mem_of_mem J (hx s) _ (Nat.pos_of_ne_zero (by simpa using hs))

end AdicMem

section LinComb

variable {T : Type*} [CommRing T] (I : Ideal T)

theorem mem_pair {u v : T} (hu : u ∈ I) (hv : v ∈ I) : ∀ s : Fin 2, (![u, v] : Fin 2 → T) s ∈ I := by
  intro s; fin_cases s <;> simpa

variable [IsAdicComplete I T] (F : FormalGroup T)

theorem eval_mem {u v : T} (hu : u ∈ I) (hv : v ∈ I) :
    (letI : WithIdeal T := ⟨I⟩; F.eval u v) ∈ I :=
  adic_eval₂_mem I (mem_pair I hu hv) F.zero_constantCoeff

theorem evalNSMul_mem {y : T} (hy : y ∈ I) (n : ℕ) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n y) ∈ I := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    show (letI : WithIdeal T := ⟨I⟩; F.eval (F.evalNSMul n y) y) ∈ I
    exact eval_mem I F ih hy

theorem linCombAdic_mem {x₀ x₁ : T} (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b ∈ I :=
  eval_mem I F (evalNSMul_mem I F hx₀ a) (evalNSMul_mem I F hx₁ b)

end LinComb

noncomputable def drinfeldPoly {T : Type*} [CommRing T] (q : ℕ) (c : ℕ → ℕ → T) : T[X] :=
  ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b))

theorem drinfeldDivisor_eq_coe {T : Type*} [CommRing T] [UniformSpace T] (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) :
    F.drinfeldDivisor q x₀ x₁ = ((drinfeldPoly q (F.linComb x₀ x₁) : T[X]) : T⟦X⟧) := by
  unfold FormalGroup.drinfeldDivisor drinfeldPoly
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

theorem drinfeldDivisorAdic_eq_coe {T : Type*} [CommRing T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    F.drinfeldDivisorAdic I q x₀ x₁ = ((drinfeldPoly q (F.linCombAdic I x₀ x₁) : T[X]) : T⟦X⟧) := by
  letI : WithIdeal T := ⟨I⟩
  exact drinfeldDivisor_eq_coe F q x₀ x₁

theorem monic_drinfeldPoly {T : Type*} [CommRing T] (q : ℕ) (c : ℕ → ℕ → T) : (drinfeldPoly q c).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_drinfeldPoly {T : Type*} [CommRing T] [Nontrivial T] (q : ℕ) (c : ℕ → ℕ → T) :
    (drinfeldPoly q c).natDegree = q * q := by
  unfold drinfeldPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ =>
    Polynomial.monic_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
  have h : ∀ a ∈ Finset.range q,
      (∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X]).natDegree = q := by
    intro a _
    rw [Polynomial.natDegree_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem isDistinguishedAt_drinfeldPoly {T : Type*} [CommRing T] (I : Ideal T) (hI : I ≠ ⊤) (q : ℕ)
    (c : ℕ → ℕ → T) (hc : ∀ a b, c a b ∈ I) : (drinfeldPoly q c).IsDistinguishedAt I := by
  haveI : Nontrivial T :=
    ⟨⟨0, 1, fun h => hI (Ideal.eq_top_of_isUnit_mem _ (Submodule.zero_mem I) (by rw [h]; exact isUnit_one))⟩⟩
  refine ⟨⟨fun {i} hi => ?_⟩, monic_drinfeldPoly q c⟩
  rw [natDegree_drinfeldPoly] at hi
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map]
  have hmap : (drinfeldPoly q c).map (Ideal.Quotient.mk I) = Polynomial.X ^ (q * q) := by
    unfold drinfeldPoly
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (hc _ _), map_zero, sub_zero, Finset.prod_const, Finset.card_range,
      ← pow_mul]
  rw [hmap, Polynomial.coeff_X_pow, if_neg (by omega)]

theorem exists_basis_of_isWeierstrassFactorizationAt {A : Type*} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    {g : A⟦X⟧} {D : A[X]} {h : A⟦X⟧} (H : g.IsWeierstrassFactorizationAt D h I) (n : ℕ) (hn : D.natDegree = n) :
    ∃ b : Module.Basis (Fin n) A (A⟦X⟧ ⧸ Ideal.span {g}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {g}) (PowerSeries.X ^ (i : ℕ)) := by
  subst hn
  let pb : PowerBasis A (AdjoinRoot D) := AdjoinRoot.powerBasis' H.isDistinguishedAt.monic
  let e : (A[X] ⧸ Ideal.span {D}) ≃ₐ[A] A⟦X⟧ ⧸ Ideal.span {g} := H.algEquivQuotient
  have hdim : pb.dim = D.natDegree := rfl
  refine ⟨(pb.basis.reindex (finCongr hdim)).map e.toLinearEquiv, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, pb.basis_eq_pow]
  have hgen : pb.gen = AdjoinRoot.root D := rfl
  rw [hgen]
  have hi : (((finCongr hdim).symm i : Fin pb.dim) : ℕ) = (i : ℕ) := by simp
  rw [hi]
  show e (AdjoinRoot.root D ^ (i : ℕ)) = _
  have hmk : ∀ p : A[X], e (AdjoinRoot.mk D p) = Ideal.Quotient.mk (Ideal.span {g}) (p : A⟦X⟧) := by
    intro p
    show H.algEquivQuotient (Ideal.Quotient.mk (Ideal.span {D}) p) = _
    rw [PowerSeries.IsWeierstrassFactorizationAt.algEquivQuotient_apply, Ideal.quotient_map_mkₐ,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
    rfl
  rw [← AdjoinRoot.mk_X, ← map_pow, hmk, Polynomial.coe_pow, Polynomial.coe_X]

end R4ConvFKR

open R4ConvFKR in

theorem solution
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (q : ℕ) (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I)
    (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    ∃ b : Module.Basis (Fin (q * q)) T (PowerSeries T ⧸ Ideal.span {F.nthSeries q}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {F.nthSeries q}) (PowerSeries.X ^ (i : ℕ)) := by
  rcases subsingleton_or_nontrivial T with hT | hT
  ·
    haveI : Subsingleton (PowerSeries T ⧸ Ideal.span {F.nthSeries q}) := Quot.Subsingleton
    haveI : Subsingleton (Fin (q * q) →₀ T) := inferInstance
    exact ⟨⟨LinearEquiv.ofSubsingleton _ _⟩, fun i => Subsingleton.elim _ _⟩
  ·
    have hI : I ≠ ⊤ := by
      intro hI
      have h1 : (1 : T) = 0 := by
        refine IsHausdorff.haus' (I := I) (M := T) 1 fun n => ?_
        rw [hI, Ideal.top_pow, Ideal.smul_eq_mul, Ideal.mul_top]
        exact SModEq.top
      exact one_ne_zero h1
    obtain ⟨u, hu, hq⟩ := (FormalGroup.isDrinfeldBasisAdic_iff F I q x₀ x₁).mp hD
    have hmem : ∀ a b, F.linCombAdic I x₀ x₁ a b ∈ I := fun a b => linCombAdic_mem I F hx₀ hx₁ a b
    have hDist : (drinfeldPoly q (F.linCombAdic I x₀ x₁)).IsDistinguishedAt I :=
      isDistinguishedAt_drinfeldPoly I hI q _ hmem
    have hfac : (F.nthSeries q).IsWeierstrassFactorizationAt (drinfeldPoly q (F.linCombAdic I x₀ x₁)) u I :=
      ⟨hDist, hu, by rw [hq, drinfeldDivisorAdic_eq_coe, mul_comm]⟩
    exact exists_basis_of_isWeierstrassFactorizationAt hfac (q * q) (natDegree_drinfeldPoly q _)

end S_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow (solution)

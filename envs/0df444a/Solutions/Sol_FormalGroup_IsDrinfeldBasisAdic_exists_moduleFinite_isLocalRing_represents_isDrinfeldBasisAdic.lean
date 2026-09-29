-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/abeb55d3-b936-5db9-b901-4ba87e189c3a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_evalSeries_nthSeries_eq_zero
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

universe u v w

section PartL

open MvPowerSeries

namespace R4aL

variable {T : Type*} [CommRing T]

noncomputable def nser (F : FormalGroup T) (i : Fin 2) : ℕ → MvPowerSeries (Fin 2) T
  | 0 => 0
  | n + 1 => subst ![nser F i n, X i] F.toPowerSeries

theorem nser_zero (F : FormalGroup T) (i : Fin 2) : nser F i 0 = 0 := rfl

theorem nser_succ (F : FormalGroup T) (i : Fin 2) (n : ℕ) :
    nser F i (n + 1) = subst ![nser F i n, X i] F.toPowerSeries := rfl

theorem constantCoeff_pair {f g : MvPowerSeries (Fin 2) T} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : ∀ s : Fin 2, constantCoeff ((![f, g] : Fin 2 → MvPowerSeries (Fin 2) T) s) = 0 := by
  intro s
  fin_cases s
  · simpa using hf
  · simpa using hg

theorem hasSubst_pair {f g : MvPowerSeries (Fin 2) T} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : HasSubst (![f, g] : Fin 2 → MvPowerSeries (Fin 2) T) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_pair hf hg)

theorem constantCoeff_nser (F : FormalGroup T) (i : Fin 2) (n : ℕ) : constantCoeff (nser F i n) = 0 := by
  induction n with
  | zero => simp [nser_zero]
  | succ n ih =>
    rw [nser_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_pair ih (constantCoeff_X i))
      (constantCoeff_pair ih (constantCoeff_X i)) F.zero_constantCoeff

theorem hasSubst_nser (F : FormalGroup T) (i : Fin 2) (n : ℕ) :
    HasSubst (![nser F i n, X i] : Fin 2 → MvPowerSeries (Fin 2) T) :=
  hasSubst_pair (constantCoeff_nser F i n) (constantCoeff_X i)

noncomputable def lam (F : FormalGroup T) (a b : ℕ) : MvPowerSeries (Fin 2) T :=
  subst ![nser F 0 a, nser F 1 b] F.toPowerSeries

theorem hasSubst_lam (F : FormalGroup T) (a b : ℕ) :
    HasSubst (![nser F 0 a, nser F 1 b] : Fin 2 → MvPowerSeries (Fin 2) T) :=
  hasSubst_pair (constantCoeff_nser F 0 a) (constantCoeff_nser F 1 b)

section Map

variable {T' : Type*} [CommRing T'] (χ : T →+* T') (F : FormalGroup T) (G : FormalGroup T')

theorem map_pair (f g : MvPowerSeries (Fin 2) T) :
    (fun s => map χ ((![f, g] : Fin 2 → MvPowerSeries (Fin 2) T) s)) = ![map χ f, map χ g] := by
  funext s
  fin_cases s <;> simp

theorem map_nser (h : F.IsBaseChange χ G) (i : Fin 2) (n : ℕ) : map χ (nser F i n) = nser G i n := by
  induction n with
  | zero => simp [nser_zero]
  | succ n ih =>
    rw [nser_succ, nser_succ, map_subst (hasSubst_nser F i n), map_pair, ih, map_X]
    unfold FormalGroup.IsBaseChange at h
    rw [h]

theorem map_lam (h : F.IsBaseChange χ G) (a b : ℕ) : map χ (lam F a b) = lam G a b := by
  unfold lam
  rw [map_subst (hasSubst_lam F a b), map_pair, map_nser χ F G h, map_nser χ F G h]
  unfold FormalGroup.IsBaseChange at h
  rw [h]

end Map

section Eval

variable (I : Ideal T)

theorem eval_eq_adicEval (F : FormalGroup T) (u v : T) :
    (letI : WithIdeal T := ⟨I⟩; F.eval u v) = MvFormalGroup.adicEval I ![u, v] F.toPowerSeries := rfl

theorem mem_radical_of_mem {x : Fin 2 → T} (hx : ∀ s, x s ∈ I) : ∀ s, x s ∈ I.radical :=
  fun s => Ideal.le_radical (hx s)

variable [IsAdicComplete I T] (F : FormalGroup T)

theorem evalNSMul_eq (x : Fin 2 → T) (hx : ∀ s, x s ∈ I) (i : Fin 2) (n : ℕ) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n (x i)) = MvFormalGroup.adicEval I x (nser F i n) := by
  induction n with
  | zero =>
    show (0 : T) = MvFormalGroup.adicEval I x (0 : MvPowerSeries (Fin 2) T)
    rw [← MvFormalGroup.coe_adicEvalAlgHom I (mem_radical_of_mem I hx), map_zero]
  | succ n ih =>
    show (letI : WithIdeal T := ⟨I⟩; F.eval (F.evalNSMul n (x i)) (x i)) = _
    rw [nser_succ, MvFormalGroup.adicEval_subst I (mem_radical_of_mem I hx) (hasSubst_nser F i n)]
    have hfam : (fun t => MvFormalGroup.adicEval I x ((![nser F i n, X i] : Fin 2 → MvPowerSeries (Fin 2) T) t)) =
        ![MvFormalGroup.adicEval I x (nser F i n), x i] := by
      funext t
      fin_cases t
      · simp
      · simp [MvFormalGroup.adicEval_X]
    rw [hfam, ← ih]
    rfl

theorem linCombAdic_eq (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b = MvFormalGroup.adicEval I ![x₀, x₁] (lam F a b) := by
  set x : Fin 2 → T := ![x₀, x₁] with hxdef
  have hx : ∀ s, x s ∈ I := by
    intro s; fin_cases s <;> simpa [hxdef]
  unfold lam
  rw [MvFormalGroup.adicEval_subst I (mem_radical_of_mem I hx) (hasSubst_lam F a b)]
  have hfam : (fun t => MvFormalGroup.adicEval I x ((![nser F 0 a, nser F 1 b] : Fin 2 → MvPowerSeries (Fin 2) T) t)) =
      ![MvFormalGroup.adicEval I x (nser F 0 a), MvFormalGroup.adicEval I x (nser F 1 b)] := by
    funext t
    fin_cases t <;> simp
  rw [hfam, ← evalNSMul_eq I F x hx 0 a, ← evalNSMul_eq I F x hx 1 b]
  rfl

end Eval

section Change

variable {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)

theorem hasEval_of_mem {σ : Type*} [Finite σ] {y : σ → B} (hy : ∀ s, y s ∈ J) :
    letI : WithIdeal B := ⟨J⟩
    MvPowerSeries.HasEval y := by
  letI : WithIdeal B := ⟨J⟩
  refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (hy s), ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

variable [IsAdicComplete I A] [IsAdicComplete J B] (χ : A →+* B)

theorem adicEval_eq_tsum {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (K : Ideal S) [IsAdicComplete K S]
    {σ : Type*} [Finite σ] (y : σ → S) (hy : ∀ s, y s ∈ K) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval K y f =
      (letI : WithIdeal S := ⟨K⟩; ∑' d : σ →₀ ℕ, algebraMap R S (coeff d f) * d.prod fun s e => y s ^ e) := by
  letI uS : WithIdeal S := ⟨K⟩
  letI uR : UniformSpace R := ⊥
  haveI : CompleteSpace S := ((IsAdic.isAdicComplete_iff (show IsAdic K from rfl)).mp ‹IsAdicComplete K S›).1
  haveI : T2Space S := ((IsAdic.isAdicComplete_iff (show IsAdic K from rfl)).mp ‹IsAdicComplete K S›).2
  have hy' : MvPowerSeries.HasEval y := hasEval_of_mem K hy
  show MvPowerSeries.eval₂ (algebraMap R S) y f = _
  rw [MvPowerSeries.eval₂_eq_tsum continuous_of_discreteTopology hy']

theorem adicEval_algebra_eq_adicEval_map {σ : Type*} [Finite σ] (y : σ → B) (hy : ∀ s, y s ∈ J)
    (f : MvPowerSeries σ A) :
    (letI : Algebra A B := χ.toAlgebra; MvFormalGroup.adicEval J y f) =
      MvFormalGroup.adicEval J y (map χ f) := by
  rw [adicEval_eq_tsum J y hy (map χ f)]
  letI : Algebra A B := χ.toAlgebra
  rw [adicEval_eq_tsum J y hy f]
  simp only [coeff_map, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem apply_adicEval {σ : Type*} [Finite σ] (x : σ → A) (hx : ∀ s, x s ∈ I) (hχ : ∀ s, χ (x s) ∈ J)
    (f : MvPowerSeries σ A) :
    χ (MvFormalGroup.adicEval I x f) = MvFormalGroup.adicEval J (fun s => χ (x s)) (map χ f) := by
  letI : Algebra A B := χ.toAlgebra
  have hx' : ∀ s, x s ∈ I.radical := fun s => Ideal.le_radical (hx s)
  let ψ : MvPowerSeries σ A →ₐ[A] B := (Algebra.ofId A B).comp (MvFormalGroup.adicEvalAlgHom I hx')
  have hψX : ∀ s, ψ (X s) = χ (x s) := by
    intro s
    show algebraMap A B (MvFormalGroup.adicEvalAlgHom I hx' (X s)) = _
    rw [MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
    rfl
  have hψ : ∀ s, ψ (X s) ∈ J.radical := fun s => (hψX s).symm ▸ Ideal.le_radical (hχ s)
  have key := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ hψ f
  have hψf : ψ f = χ (MvFormalGroup.adicEval I x f) := by
    show algebraMap A B (MvFormalGroup.adicEvalAlgHom I hx' f) = _
    rw [MvFormalGroup.coe_adicEvalAlgHom]
    rfl
  rw [← hψf, key, funext hψX]
  exact adicEval_algebra_eq_adicEval_map J χ _ hχ f

end Change

end R4aL

theorem R4aL.apply_linCombAdic_eq_of_apply_mem
    {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B]
    (χ : A →+* B) (F : FormalGroup A) (G : FormalGroup B) (h : F.IsBaseChange χ G)
    (x₀ x₁ : A) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hχ₀ : χ x₀ ∈ J) (hχ₁ : χ x₁ ∈ J) (a b : ℕ) :
    χ (F.linCombAdic I x₀ x₁ a b) = G.linCombAdic J (χ x₀) (χ x₁) a b := by
  have hx : ∀ s, (![x₀, x₁] : Fin 2 → A) s ∈ I := by
    intro s; fin_cases s <;> simpa
  have hχ : ∀ s, χ ((![x₀, x₁] : Fin 2 → A) s) ∈ J := by
    intro s; fin_cases s <;> simpa
  have hfam : (fun s => χ ((![x₀, x₁] : Fin 2 → A) s)) = ![χ x₀, χ x₁] := by
    funext s; fin_cases s <;> simp
  rw [R4aL.linCombAdic_eq I F x₀ x₁ hx₀ hx₁, R4aL.linCombAdic_eq J G (χ x₀) (χ x₁) hχ₀ hχ₁,
    R4aL.apply_adicEval I J χ _ hx hχ, hfam, R4aL.map_lam χ F G h]

end PartL

section PartE

open PowerSeries Polynomial

namespace R4aE

theorem exists_isUnit_eq_mul_iff_eq_of_isWeierstrassFactorization
    {B : Type*} [CommRing B] [IsLocalRing B] [IsHausdorff (IsLocalRing.maximalIdeal B) B]
    {g : B⟦X⟧} {P : B[X]} {u : B⟦X⟧} (hfac : g.IsWeierstrassFactorization P u)
    (D : B[X]) (hD : D.Monic) (hdeg : D.natDegree = P.natDegree) :
    (∃ w : B⟦X⟧, IsUnit w ∧ g = w * (D : B⟦X⟧)) ↔ D = P := by
  constructor
  · rintro ⟨w, hw, hgw⟩

    have hred : (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree *
          PowerSeries.map (IsLocalRing.residue B) u =
        PowerSeries.map (IsLocalRing.residue B) w * ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) :
          (IsLocalRing.ResidueField B)⟦X⟧) := by
      have e := congrArg (PowerSeries.map (IsLocalRing.residue B)) (hfac.eq_mul.symm.trans hgw)
      rw [map_mul, map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe] at e
      have hP : P.map (IsLocalRing.residue B) = Polynomial.X ^ P.natDegree :=
        hfac.isDistinguishedAt.map_eq_X_pow
      rw [hP, Polynomial.coe_pow, Polynomial.coe_X] at e
      exact e

    have hwu : IsUnit (PowerSeries.map (IsLocalRing.residue B) w) := hw.map _
    obtain ⟨wi, hwi⟩ := hwu.exists_left_inv
    have hDbar : ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧) =
        (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree * (PowerSeries.map (IsLocalRing.residue B) u * wi) := by
      calc ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧)
          = wi * (PowerSeries.map (IsLocalRing.residue B) w *
              ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧)) := by
            rw [← mul_assoc, hwi, one_mul]
        _ = (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree *
              (PowerSeries.map (IsLocalRing.residue B) u * wi) := by
            rw [← hred]; ring
    have hdist : D.IsDistinguishedAt (IsLocalRing.maximalIdeal B) := by
      refine ⟨⟨fun {i} hi => ?_⟩, hD⟩
      rw [← IsLocalRing.residue_eq_zero_iff]
      have hc := congrArg (PowerSeries.coeff i) hDbar
      rw [Polynomial.coeff_coe, Polynomial.coeff_map, PowerSeries.coeff_X_pow_mul', if_neg (by omega)] at hc
      exact hc
    have hfac' : g.IsWeierstrassFactorization D w := ⟨hdist, hw, by rw [hgw, mul_comm]⟩
    exact (hfac'.elim hfac).1
  · rintro rfl
    exact ⟨u, hfac.isUnit, by rw [hfac.eq_mul, mul_comm]⟩

theorem drinfeldDivisor_eq_coe {T : Type*} [CommRing T] [UniformSpace T] (F : FormalGroup T) (q : ℕ) (x₀ x₁ : T) :
    F.drinfeldDivisor q x₀ x₁ =
      ((∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (F.linComb x₀ x₁ a b)) : T[X]) :
        T⟦X⟧) := by
  unfold FormalGroup.drinfeldDivisor
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

theorem drinfeldDivisorAdic_eq_coe {T : Type*} [CommRing T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    F.drinfeldDivisorAdic I q x₀ x₁ =
      ((∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (F.linCombAdic I x₀ x₁ a b)) : T[X]) :
        T⟦X⟧) := by
  letI : WithIdeal T := ⟨I⟩
  exact drinfeldDivisor_eq_coe F q x₀ x₁

theorem monic_prod_X_sub_C {T : Type*} [CommRing T] (q : ℕ) (c : ℕ → ℕ → T) :
    (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X]).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_prod_X_sub_C {T : Type*} [CommRing T] [Nontrivial T] (q : ℕ) (c : ℕ → ℕ → T) :
    (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X]).natDegree = q * q := by
  rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ =>
    Polynomial.monic_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
  have h : ∀ a ∈ Finset.range q,
      (∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X]).natDegree = q := by
    intro a _
    rw [Polynomial.natDegree_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem isDistinguishedAt_prod_X_sub_C {T : Type*} [CommRing T] (I : Ideal T) (hI : I ≠ ⊤) (q : ℕ) (c : ℕ → ℕ → T)
    (hc : ∀ a b, c a b ∈ I) :
    (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X]).IsDistinguishedAt I := by
  haveI : Nontrivial T := ⟨⟨0, 1, fun h => hI (Ideal.eq_top_of_isUnit_mem _ (Submodule.zero_mem I) (by rw [h]; exact isUnit_one))⟩⟩
  refine ⟨⟨fun {i} hi => ?_⟩, monic_prod_X_sub_C q c⟩
  rw [natDegree_prod_X_sub_C] at hi
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map]
  have hmap : ((∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a b)) : T[X])).map
      (Ideal.Quotient.mk I) = Polynomial.X ^ (q * q) := by
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (hc _ _), map_zero, sub_zero, Finset.prod_const, Finset.card_range,
      ← pow_mul]
  rw [hmap, Polynomial.coeff_X_pow, if_neg (by omega)]

section Mem

variable {T : Type*} [CommRing T] (I : Ideal T)

theorem mem_pair_radical {u v : T} (hu : u ∈ I.radical) (hv : v ∈ I.radical) :
    ∀ s : Fin 2, (![u, v] : Fin 2 → T) s ∈ I.radical := by
  intro s; fin_cases s <;> simpa

variable [IsAdicComplete I T] (F : FormalGroup T)

theorem evalNSMul_mem_radical {y : T} (hy : y ∈ I) (n : ℕ) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n y) ∈ I.radical := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    show (letI : WithIdeal T := ⟨I⟩; F.eval (F.evalNSMul n y) y) ∈ I.radical
    exact MvFormalGroup.adicEval_mem_radical I (mem_pair_radical I ih (Ideal.le_radical hy)) F.zero_constantCoeff

theorem linCombAdic_mem_radical {y₀ y₁ : T} (hy₀ : y₀ ∈ I) (hy₁ : y₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I y₀ y₁ a b ∈ I.radical :=
  MvFormalGroup.adicEval_mem_radical I
    (mem_pair_radical I (evalNSMul_mem_radical I F hy₀ a) (evalNSMul_mem_radical I F hy₁ b)) F.zero_constantCoeff

end Mem

end R4aE

open IsLocalRing in

theorem R4aE.isDrinfeldBasisAdic_iff_dpoly_eq
    {T : Type*} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) (P : Polynomial T) (U : PowerSeries T)
    (hP : P.Monic) (hdeg : P.natDegree = q * q) (hU : IsUnit U)
    (hq : F.nthSeries q = (P : PowerSeries T) * U)
    (y₀ y₁ : T) (hy₀ : y₀ ∈ maximalIdeal T) (hy₁ : y₁ ∈ maximalIdeal T) :
    F.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ ↔
      (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
        (Polynomial.X - Polynomial.C (F.linCombAdic (maximalIdeal T) y₀ y₁ a b))) = P := by
  set D : T[X] := ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
        (Polynomial.X - Polynomial.C (F.linCombAdic (maximalIdeal T) y₀ y₁ a b)) with hDdef
  have hmem : ∀ a b, F.linCombAdic (maximalIdeal T) y₀ y₁ a b ∈ maximalIdeal T := by
    intro a b
    have h := R4aE.linCombAdic_mem_radical (maximalIdeal T) F hy₀ hy₁ a b
    rwa [Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal T).isPrime] at h
  have hDist : D.IsDistinguishedAt (maximalIdeal T) :=
    R4aE.isDistinguishedAt_prod_X_sub_C _ (IsLocalRing.maximalIdeal.isMaximal T).ne_top q _ hmem

  have hiff : F.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ ↔
      ∃ w : T⟦X⟧, IsUnit w ∧ F.nthSeries q = w * (D : T⟦X⟧) := by
    rw [FormalGroup.isDrinfeldBasisAdic_iff, R4aE.drinfeldDivisorAdic_eq_coe]
  rw [hiff]
  constructor
  · rintro ⟨w, hw, hqw⟩

    have hfacD : (F.nthSeries q).IsWeierstrassFactorization D w := ⟨hDist, hw, by rw [hqw, mul_comm]⟩
    have hdegP : P.natDegree = D.natDegree := by
      rw [hdeg, hDdef, R4aE.natDegree_prod_X_sub_C]
    have h := (R4aE.exists_isUnit_eq_mul_iff_eq_of_isWeierstrassFactorization hfacD P hP hdegP).mp
      ⟨U, hU, by rw [hq, mul_comm]⟩
    exact h.symm
  · intro hDP
    exact ⟨U, hU, by rw [hDP, hq, mul_comm]⟩

end PartE

section PartA

open Polynomial IsLocalRing

namespace R4aA

theorem aeval_sub_algebraMap_coeff_zero_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x : A) (p : R[X]) :
    aeval x p - algebraMap R A (p.coeff 0) ∈ Ideal.span ({x} : Set A) := by
  rw [Ideal.mem_span_singleton']
  refine ⟨aeval x p.divX, ?_⟩
  have h := congrArg (aeval x) (Polynomial.X_mul_divX_add p)
  rw [map_add, map_mul, aeval_X, aeval_C] at h
  rw [← h]
  ring

theorem mem_of_aeval_eq_zero_of_coeff_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {P : R[X]} (hP : P.Monic) (𝔫 : Ideal A) [𝔫.IsPrime]
    (hcoef : ∀ i, i < P.natDegree → algebraMap R A (P.coeff i) ∈ 𝔫) {x : A} (hx : aeval x P = 0) : x ∈ 𝔫 := by
  apply Ideal.IsPrime.mem_of_pow_mem ‹𝔫.IsPrime› P.natDegree
  have h := hx
  rw [hP.as_sum, map_add, map_pow, aeval_X, map_sum] at h
  have hsum : ∑ i ∈ Finset.range P.natDegree, aeval x (C (P.coeff i) * X ^ i) ∈ 𝔫 := by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X]
    exact Ideal.mul_mem_right _ _ (hcoef i (Finset.mem_range.mp hi))
  have : x ^ P.natDegree = -(∑ i ∈ Finset.range P.natDegree, aeval x (C (P.coeff i) * X ^ i)) :=
    eq_neg_of_add_eq_zero_left h
  rw [this]
  exact Submodule.neg_mem _ hsum

section Amb

variable {S : Type u} [CommRing S] (P : S[X])

abbrev A₁ : Type u := AdjoinRoot P

abbrev Amb : Type u := AdjoinRoot (P.map (algebraMap S (A₁ P)))

noncomputable def x₀ : Amb P := AdjoinRoot.root (P.map (algebraMap S (A₁ P)))

noncomputable def x₁ : Amb P := AdjoinRoot.of (P.map (algebraMap S (A₁ P))) (AdjoinRoot.root P)

theorem aeval_x₀ : aeval (x₀ P) P = 0 := by
  rw [← Polynomial.aeval_map_algebraMap (A₁ P) (x₀ P) P, x₀, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem aeval_x₁ : aeval (x₁ P) P = 0 := by
  have : x₁ P = algebraMap (A₁ P) (Amb P) (AdjoinRoot.root P) := rfl
  rw [this, Polynomial.aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem finite_amb (hP : P.Monic) : Module.Finite S (Amb P) := by
  haveI : Module.Finite S (A₁ P) := hP.finite_adjoinRoot
  haveI : Module.Finite (A₁ P) (Amb P) := (hP.map (algebraMap S (A₁ P))).finite_adjoinRoot
  exact Module.Finite.trans (A₁ P) (Amb P)

noncomputable def bb : Ideal (Amb P) := Ideal.span {x₀ P, x₁ P}

theorem exists_sub_algebraMap_mem_bb (a : Amb P) : ∃ c : S, a - algebraMap S (Amb P) c ∈ bb P := by
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨s', hs'⟩ := AdjoinRoot.mk_surjective (r.coeff 0)
  refine ⟨s'.coeff 0, ?_⟩
  have h1 : AdjoinRoot.mk _ r - algebraMap (A₁ P) (Amb P) (r.coeff 0) ∈ bb P := by
    rw [← AdjoinRoot.aeval_eq]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      (aeval_sub_algebraMap_coeff_zero_mem (x₀ P) r)
  have h2 : algebraMap (A₁ P) (Amb P) (r.coeff 0) - algebraMap S (Amb P) (s'.coeff 0) ∈ bb P := by
    rw [← hs', ← AdjoinRoot.aeval_eq, IsScalarTower.algebraMap_apply S (A₁ P) (Amb P), ← map_sub]
    obtain ⟨t, ht⟩ := (Ideal.mem_span_singleton').mp (aeval_sub_algebraMap_coeff_zero_mem (AdjoinRoot.root P) s')
    rw [← ht, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_sub_cancel] at this

section Lift

variable {B : Type w} [CommRing B] [Algebra S B]

noncomputable def lift₁ (y₁ : B) (h₁ : aeval y₁ P = 0) : A₁ P →ₐ[S] B :=
  AdjoinRoot.liftAlgHom P (Algebra.ofId S B) y₁ (by
    rw [← h₁, Polynomial.aeval_def]; rfl)

theorem lift₁_root (y₁ : B) (h₁ : aeval y₁ P = 0) : lift₁ P y₁ h₁ (AdjoinRoot.root P) = y₁ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem eval₂_lift₁_eq_zero (y₀ y₁ : B) (h₀ : aeval y₀ P = 0) (h₁ : aeval y₁ P = 0) :
    (P.map (algebraMap S (A₁ P))).eval₂ (lift₁ P y₁ h₁ : A₁ P →ₐ[S] B) y₀ = 0 := by
  rw [Polynomial.eval₂_map]
  have : ((lift₁ P y₁ h₁ : A₁ P →ₐ[S] B) : A₁ P →+* B).comp (algebraMap S (A₁ P)) = algebraMap S B :=
    (lift₁ P y₁ h₁).comp_algebraMap
  rw [this, ← Polynomial.aeval_def, h₀]

noncomputable def lift₂ (y₀ y₁ : B) (h₀ : aeval y₀ P = 0) (h₁ : aeval y₁ P = 0) : Amb P →ₐ[S] B :=
  AdjoinRoot.liftAlgHom (P.map (algebraMap S (A₁ P))) (lift₁ P y₁ h₁) y₀ (eval₂_lift₁_eq_zero P y₀ y₁ h₀ h₁)

theorem lift₂_x₀ (y₀ y₁ : B) (h₀ : aeval y₀ P = 0) (h₁ : aeval y₁ P = 0) : lift₂ P y₀ y₁ h₀ h₁ (x₀ P) = y₀ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem lift₂_x₁ (y₀ y₁ : B) (h₀ : aeval y₀ P = 0) (h₁ : aeval y₁ P = 0) : lift₂ P y₀ y₁ h₀ h₁ (x₁ P) = y₁ :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (lift₁_root P y₁ h₁)

theorem algHom_ext_amb {χ χ' : Amb P →ₐ[S] B} (h0 : χ (x₀ P) = χ' (x₀ P)) (h1 : χ (x₁ P) = χ' (x₁ P)) : χ = χ' := by
  refine AdjoinRoot.algHom_ext' ?_ h0
  refine AdjoinRoot.algHom_ext ?_
  exact h1

theorem existsUnique_lift (y₀ y₁ : B) (h₀ : aeval y₀ P = 0) (h₁ : aeval y₁ P = 0) :
    ∃! χ : Amb P →ₐ[S] B, χ (x₀ P) = y₀ ∧ χ (x₁ P) = y₁ :=
  ⟨lift₂ P y₀ y₁ h₀ h₁, ⟨lift₂_x₀ P y₀ y₁ h₀ h₁, lift₂_x₁ P y₀ y₁ h₀ h₁⟩, fun _ hχ' =>
    algHom_ext_amb P (hχ'.1.trans (lift₂_x₀ P y₀ y₁ h₀ h₁).symm) (hχ'.2.trans (lift₂_x₁ P y₀ y₁ h₀ h₁).symm)⟩

end Lift

section Local

variable [IsLocalRing S] {k : Type v} [Field k] (resS : S →+* k)

theorem aeval_zero_eq_zero (hkerS : RingHom.ker resS = maximalIdeal S) (hP : P.IsDistinguishedAt (maximalIdeal S))
    (hP0 : 0 < P.natDegree) : letI : Algebra S k := resS.toAlgebra; aeval (0 : k) P = 0 := by
  letI : Algebra S k := resS.toAlgebra
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
  show resS (P.coeff 0) = 0
  rw [← RingHom.mem_ker, hkerS]
  exact hP.mem hP0

structure ResData (S : Type u) [CommRing S] [IsLocalRing S] (P : S[X]) (k : Type v) [Field k] where
  resS : S →+* k
  hresS : Function.Surjective resS
  hkerS : RingHom.ker resS = maximalIdeal S
  hP : P.IsDistinguishedAt (maximalIdeal S)
  hP0 : 0 < P.natDegree

variable {P}

noncomputable def resA (d : ResData S P k) : Amb P →+* k :=
  letI : Algebra S k := d.resS.toAlgebra
  (lift₂ P (0 : k) 0 (aeval_zero_eq_zero P d.resS d.hkerS d.hP d.hP0)
    (aeval_zero_eq_zero P d.resS d.hkerS d.hP d.hP0)).toRingHom

theorem resA_algebraMap (d : ResData S P k) (s : S) : resA d (algebraMap S (Amb P) s) = d.resS s := by
  letI : Algebra S k := d.resS.toAlgebra
  exact (lift₂ P (0 : k) 0 (aeval_zero_eq_zero P d.resS d.hkerS d.hP d.hP0)
    (aeval_zero_eq_zero P d.resS d.hkerS d.hP d.hP0)).commutes s

theorem resA_x₀ (d : ResData S P k) : resA d (x₀ P) = 0 := by
  letI : Algebra S k := d.resS.toAlgebra
  exact lift₂_x₀ P (0 : k) 0 _ _

theorem resA_x₁ (d : ResData S P k) : resA d (x₁ P) = 0 := by
  letI : Algebra S k := d.resS.toAlgebra
  exact lift₂_x₁ P (0 : k) 0 _ _

theorem resA_surjective (d : ResData S P k) : Function.Surjective (resA d) := fun t => by
  obtain ⟨s, rfl⟩ := d.hresS t
  exact ⟨algebraMap S (Amb P) s, resA_algebraMap d s⟩

theorem bb_le_ker (d : ResData S P k) : bb P ≤ RingHom.ker (resA d) := by
  rw [bb, Ideal.span_le]
  rintro x (rfl | rfl)
  · exact resA_x₀ d
  · exact resA_x₁ d

theorem ker_isMaximal (d : ResData S P k) : (RingHom.ker (resA d)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (resA_surjective d)

theorem eq_ker_of_isMaximal (d : ResData S P k) (𝔫 : Ideal (Amb P)) [h𝔫 : 𝔫.IsMaximal] : 𝔫 = RingHom.ker (resA d) := by
  haveI : Module.Finite S (Amb P) := finite_amb P d.hP.monic

  have hunder : ∀ s ∈ maximalIdeal S, algebraMap S (Amb P) s ∈ 𝔫 := by
    intro s hs
    have hmax : (𝔫.comap (algebraMap S (Amb P))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
    have heq : 𝔫.comap (algebraMap S (Amb P)) = maximalIdeal S := IsLocalRing.eq_maximalIdeal hmax
    rw [← heq] at hs
    exact hs

  have hcoef : ∀ i, i < P.natDegree → algebraMap S (Amb P) (P.coeff i) ∈ 𝔫 := fun i hi => hunder _ (d.hP.mem hi)
  have hx₀ : x₀ P ∈ 𝔫 := mem_of_aeval_eq_zero_of_coeff_mem d.hP.monic 𝔫 hcoef (aeval_x₀ P)
  have hx₁ : x₁ P ∈ 𝔫 := mem_of_aeval_eq_zero_of_coeff_mem d.hP.monic 𝔫 hcoef (aeval_x₁ P)
  have hbb : bb P ≤ 𝔫 := by
    rw [bb, Ideal.span_le]
    rintro x (rfl | rfl)
    exacts [hx₀, hx₁]

  symm
  refine (ker_isMaximal d).eq_of_le h𝔫.ne_top ?_
  intro a ha
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_bb P a
  have hc0 : d.resS c = 0 := by
    have h1 : resA d (a - algebraMap S (Amb P) c) = 0 := bb_le_ker d hc
    rw [map_sub, RingHom.mem_ker.mp ha, resA_algebraMap, zero_sub, neg_eq_zero] at h1
    exact h1
  have hcm : c ∈ maximalIdeal S := by rw [← d.hkerS]; exact hc0
  have : a = (a - algebraMap S (Amb P) c) + algebraMap S (Amb P) c := by ring
  rw [this]
  exact Ideal.add_mem _ (hbb hc) (hunder c hcm)

theorem isLocalRing_amb (d : ResData S P k) : IsLocalRing (Amb P) :=
  IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker (resA d), ker_isMaximal d, fun 𝔫 h𝔫 => eq_ker_of_isMaximal d 𝔫 (h𝔫 := h𝔫)⟩

theorem ker_resA_eq (d : ResData S P k) :
    RingHom.ker (resA d) = @maximalIdeal (Amb P) _ (isLocalRing_amb d) := by
  letI := isLocalRing_amb d
  exact IsLocalRing.eq_maximalIdeal (ker_isMaximal d)

theorem isLocalHom_algebraMap (d : ResData S P k) :
    IsLocalHom (algebraMap S (Amb P)) := by
  letI := isLocalRing_amb d
  refine ⟨fun s hs => ?_⟩
  by_contra hns
  have hsm : s ∈ maximalIdeal S := hns
  rw [← d.hkerS, RingHom.mem_ker] at hsm
  have : algebraMap S (Amb P) s ∈ maximalIdeal (Amb P) := by
    rw [← ker_resA_eq d, RingHom.mem_ker, resA_algebraMap, hsm]
  exact (IsLocalRing.mem_maximalIdeal _).mp this hs

end Local

end Amb

end R4aA

theorem R4aA.exists_amb
    {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    {k : Type v} [Field k] (resS : S →+* k) (hresS : Function.Surjective resS)
    (hkerS : RingHom.ker resS = maximalIdeal S)
    {P : Polynomial S} (hP : P.IsDistinguishedAt (maximalIdeal S)) (hP0 : 0 < P.natDegree) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra S A) (_ : IsLocalRing A) (_ : Module.Finite S A)
      (_ : IsAdicComplete (maximalIdeal A) A)
      (resA : A →+* k) (_ : Function.Surjective resA) (_ : RingHom.ker resA = maximalIdeal A)
      (_ : ∀ s : S, resA (algebraMap S A s) = resS s)
      (x₀ x₁ : A) (_ : x₀ ∈ maximalIdeal A) (_ : x₁ ∈ maximalIdeal A)
      (_ : Polynomial.aeval x₀ P = 0) (_ : Polynomial.aeval x₁ P = 0),
      ∀ (B : Type w) [CommRing B] [Algebra S B] (y₀ y₁ : B),
        Polynomial.aeval y₀ P = 0 → Polynomial.aeval y₁ P = 0 →
          ∃! χ : A →ₐ[S] B, χ x₀ = y₀ ∧ χ x₁ = y₁ := by
  let d : R4aA.ResData S P k := ⟨resS, hresS, hkerS, hP, hP0⟩
  haveI hloc : IsLocalRing (R4aA.Amb P) := R4aA.isLocalRing_amb d
  haveI hfin : Module.Finite S (R4aA.Amb P) := R4aA.finite_amb P hP.monic
  haveI hlh : IsLocalHom (algebraMap S (R4aA.Amb P)) := R4aA.isLocalHom_algebraMap d
  have hker : RingHom.ker (R4aA.resA d) = maximalIdeal (R4aA.Amb P) := R4aA.ker_resA_eq d
  haveI hcpl : IsAdicComplete (maximalIdeal (R4aA.Amb P)) (R4aA.Amb P) := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := S)
  refine ⟨R4aA.Amb P, inferInstance, inferInstance, hloc, hfin, hcpl, R4aA.resA d,
    R4aA.resA_surjective d, hker, R4aA.resA_algebraMap d, R4aA.x₀ P, R4aA.x₁ P, ?_, ?_,
    R4aA.aeval_x₀ P, R4aA.aeval_x₁ P, fun B _ _ y₀ y₁ h₀ h₁ => R4aA.existsUnique_lift P y₀ y₁ h₀ h₁⟩
  · rw [← hker, RingHom.mem_ker]; exact R4aA.resA_x₀ d
  · rw [← hker, RingHom.mem_ker]; exact R4aA.resA_x₁ d

end PartA

section PartP

open FormalGroup IsLocalRing Polynomial

namespace R4aP

noncomputable def dpoly {T : Type*} [CommRing T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) : T[X] :=
  ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q, (Polynomial.X - Polynomial.C (F.linCombAdic I x₀ x₁ a b))

theorem dpoly_map {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B]
    (χ : A →+* B) (F : FormalGroup A) (G : FormalGroup B) (h : F.IsBaseChange χ G)
    (q : ℕ) (x₀ x₁ : A) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hχ₀ : χ x₀ ∈ J) (hχ₁ : χ x₁ ∈ J) :
    (dpoly F I q x₀ x₁).map χ = dpoly G J q (χ x₀) (χ x₁) := by
  unfold dpoly
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    R4aL.apply_linCombAdic_eq_of_apply_mem I J χ F G h x₀ x₁ hx₀ hx₁ hχ₀ hχ₁ a b]

theorem monic_dpoly {T : Type*} [CommRing T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    (dpoly F I q x₀ x₁).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_dpoly {T : Type*} [CommRing T] [Nontrivial T] (F : FormalGroup T) (I : Ideal T) (q : ℕ) (x₀ x₁ : T) :
    (dpoly F I q x₀ x₁).natDegree = q * q := by
  unfold dpoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ =>
    Polynomial.monic_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
  have h : ∀ a ∈ Finset.range q, (∏ b ∈ Finset.range q,
      (Polynomial.X - Polynomial.C (F.linCombAdic I x₀ x₁ a b)) : T[X]).natDegree = q := by
    intro a _
    rw [Polynomial.natDegree_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem isDistinguishedAt_dpoly {T : Type*} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) {x₀ x₁ : T} (hx₀ : x₀ ∈ maximalIdeal T) (hx₁ : x₁ ∈ maximalIdeal T) :
    (dpoly F (maximalIdeal T) q x₀ x₁).IsDistinguishedAt (maximalIdeal T) := by
  have hc : ∀ a b, F.linCombAdic (maximalIdeal T) x₀ x₁ a b ∈ maximalIdeal T := by
    intro a b
    have h := R4aE.linCombAdic_mem_radical (maximalIdeal T) F hx₀ hx₁ a b
    rwa [Ideal.IsPrime.radical (IsLocalRing.maximalIdeal.isMaximal T).isPrime] at h
  refine ⟨⟨fun {i} hi => ?_⟩, monic_dpoly F _ q x₀ x₁⟩
  rw [natDegree_dpoly] at hi
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map]
  have hmap : (dpoly F (maximalIdeal T) q x₀ x₁).map (Ideal.Quotient.mk (maximalIdeal T)) = Polynomial.X ^ (q * q) := by
    unfold dpoly
    rw [Polynomial.map_prod]
    simp_rw [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      (Ideal.Quotient.eq_zero_iff_mem).mpr (hc _ _), map_zero, sub_zero, Finset.prod_const, Finset.card_range,
      ← pow_mul]
  rw [hmap, Polynomial.coeff_X_pow, if_neg (by omega)]

theorem adicEval_coe_polynomial {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (K : Ideal S) (y : S) (p : R[X]) :
    MvFormalGroup.adicEval K (fun _ : Unit => y) (p : PowerSeries R) = p.eval₂ (algebraMap R S) y := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨K⟩
  exact PowerSeries.eval₂_coe (algebraMap R S) y p

theorem aeval_eq_zero_of_evalSeries_eq_zero {S B : Type*} [CommRing S] [CommRing B] [Algebra S B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] (G : FormalGroup B) (q : ℕ) (P : S[X]) (U : PowerSeries S)
    (hU : IsUnit U) (hq : G.nthSeries q = ((P.map (algebraMap S B) : B[X]) : PowerSeries B) * PowerSeries.map (algebraMap S B) U)
    (y : B) (hy : y ∈ maximalIdeal B)
    (hev : (letI : WithIdeal B := ⟨maximalIdeal B⟩; FormalGroup.evalSeries (G.nthSeries q) y) = 0) :
    aeval y P = 0 := by
  have hyr : ∀ s : Unit, (fun _ : Unit => y) s ∈ (maximalIdeal B).radical := fun _ => Ideal.le_radical hy
  have hbridge : (letI : WithIdeal B := ⟨maximalIdeal B⟩; FormalGroup.evalSeries (G.nthSeries q) y) =
      MvFormalGroup.adicEval (maximalIdeal B) (fun _ : Unit => y) (G.nthSeries q) := rfl
  rw [hbridge, hq, ← MvFormalGroup.coe_adicEvalAlgHom (maximalIdeal B) hyr, map_mul,
    MvFormalGroup.coe_adicEvalAlgHom, adicEval_coe_polynomial] at hev
  have hunit : IsUnit (MvFormalGroup.adicEvalAlgHom (R := B) (maximalIdeal B) hyr (PowerSeries.map (algebraMap S B) U)) :=
    (hU.map _).map _
  rw [MvFormalGroup.coe_adicEvalAlgHom] at hunit
  have h0 : (P.map (algebraMap S B)).eval₂ (algebraMap B B) y = 0 := hunit.mul_left_eq_zero.mp hev
  rw [Algebra.algebraMap_self, Polynomial.eval₂_id, Polynomial.eval_map] at h0
  rwa [Polynomial.aeval_def]

end R4aP

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra (PowerSeries W₀) C) (_ : IsLocalRing C)
      (_ : Module.Finite (PowerSeries W₀) C) (_ : IsAdicComplete (maximalIdeal C) C)
      (resC : C →+* k) (_ : Function.Surjective resC) (_ : RingHom.ker resC = maximalIdeal C)
      (_ : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) C f) = res₀ (PowerSeries.constantCoeff f))
      (Gc : FormalGroup C) (_ : Fu.IsBaseChange (algebraMap (PowerSeries W₀) C) Gc)
      (x₀ x₁ : C) (_ : x₀ ∈ maximalIdeal C) (_ : x₁ ∈ maximalIdeal C)
      (_ : Gc.IsDrinfeldBasisAdic (maximalIdeal C) q x₀ x₁),
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra (PowerSeries W₀) B] [IsAdicComplete (maximalIdeal B) B]
        (G : FormalGroup B), Fu.IsBaseChange (algebraMap (PowerSeries W₀) B) G →
        ∀ (y₀ y₁ : B), y₀ ∈ maximalIdeal B → y₁ ∈ maximalIdeal B →
          G.IsDrinfeldBasisAdic (maximalIdeal B) q y₀ y₁ →
          ∃! χ : C →ₐ[PowerSeries W₀] B, χ x₀ = y₀ ∧ χ x₁ = y₁ := by
  have hqp : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hqp.two_le

  haveI : IsAdicComplete (maximalIdeal (PowerSeries W₀)) (PowerSeries W₀) :=
    MvPowerSeries.isAdicComplete_maximalIdeal (σ := Unit) (R := W₀)

  obtain ⟨P, U, hPmonic, hPdeg, hPcoef, hU, hfac⟩ :=
    FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul q k W₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu
  have hP : P.IsDistinguishedAt (maximalIdeal (PowerSeries W₀)) := ⟨⟨fun {i} hi => hPcoef i (hPdeg ▸ hi)⟩, hPmonic⟩
  have hP0 : 0 < P.natDegree := by rw [hPdeg]; exact Nat.mul_pos hqp.pos hqp.pos

  set resS : PowerSeries W₀ →+* k := res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) with hresSdef
  have hresS : Function.Surjective resS := by
    intro t
    obtain ⟨w, rfl⟩ := hres₀ t
    exact ⟨PowerSeries.C w, by simp [hresSdef]⟩
  have hkerS : RingHom.ker resS = maximalIdeal (PowerSeries W₀) := by
    ext f
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      hresSdef, RingHom.comp_apply, ← RingHom.mem_ker, hker₀, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

  obtain ⟨A, _instCR, _instAlg, _instLoc, _instFin, _instCpl, resA, hresA, hkerA, hcompA, x₀, x₁, hx₀, hx₁,
      hPx₀, hPx₁, huniv⟩ :=
    R4aA.exists_amb.{0, 0, 0}
      resS hresS hkerS hP hP0

  set Ga : FormalGroup A := Fu.map (algebraMap (PowerSeries W₀) A) with hGadef
  have hGa : Fu.IsBaseChange (algebraMap (PowerSeries W₀) A) Ga := rfl
  set PA : A[X] := P.map (algebraMap (PowerSeries W₀) A) with hPAdef
  set DA : A[X] := R4aP.dpoly Ga (maximalIdeal A) q x₀ x₁ with hDAdef
  set J : Ideal A := Ideal.span (Set.range fun i : ℕ => (DA - PA).coeff i) with hJdef
  have hmemS : ∀ s ∈ maximalIdeal (PowerSeries W₀), algebraMap (PowerSeries W₀) A s ∈ maximalIdeal A := by
    intro s hs
    rw [← hkerA, RingHom.mem_ker, hcompA, ← RingHom.mem_ker, hkerS]
    exact hs
  have hPA : PA.IsDistinguishedAt (maximalIdeal A) := by
    refine ⟨⟨fun {i} hi => ?_⟩, hPmonic.map _⟩
    rw [hPAdef, hPmonic.natDegree_map] at hi
    rw [hPAdef, Polynomial.coeff_map]
    exact hmemS _ (hP.mem hi)
  have hPAdeg : PA.natDegree = q * q := by rw [hPAdef, hPmonic.natDegree_map, hPdeg]
  have hDA : DA.IsDistinguishedAt (maximalIdeal A) := R4aP.isDistinguishedAt_dpoly Ga q hx₀ hx₁
  have hJle : J ≤ maximalIdeal A := by
    rw [hJdef, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalRing.residue_eq_zero_iff]
    show Ideal.Quotient.mk (maximalIdeal A) ((DA - PA).coeff i) = 0
    rw [← Polynomial.coeff_map, Polynomial.map_sub, hDA.map_eq_X_pow, hPA.map_eq_X_pow, R4aP.natDegree_dpoly, hPAdeg,
      sub_self, Polynomial.coeff_zero]
  have hJtop : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hJle))

  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI hlocC : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI hfinC : Module.Finite (PowerSeries W₀) (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ (PowerSeries W₀) J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (PowerSeries W₀) J)
  have hJker : ∀ a ∈ J, resA a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hkerA]; exact hJle ha
  set resC : A ⧸ J →+* k := Ideal.Quotient.lift J resA hJker with hresCdef
  have hresC : Function.Surjective resC := by
    intro t
    obtain ⟨a, rfl⟩ := hresA t
    exact ⟨Ideal.Quotient.mk J a, Ideal.Quotient.lift_mk J resA hJker⟩
  have hkerC : RingHom.ker resC = maximalIdeal (A ⧸ J) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resC hresC)
  have halgC : ∀ f : PowerSeries W₀, algebraMap (PowerSeries W₀) (A ⧸ J) f =
      Ideal.Quotient.mk J (algebraMap (PowerSeries W₀) A f) := fun f => rfl
  have hcompC : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) (A ⧸ J) f) =
      res₀ (PowerSeries.constantCoeff f) := by
    intro f
    rw [halgC, hresCdef, Ideal.Quotient.lift_mk, hcompA]
    rfl
  haveI : IsLocalHom (algebraMap (PowerSeries W₀) (A ⧸ J)) := by
    refine ⟨fun f hf => ?_⟩
    by_contra hnf
    have hfm : f ∈ maximalIdeal (PowerSeries W₀) := hnf
    rw [← hkerS, RingHom.mem_ker] at hfm
    have : algebraMap (PowerSeries W₀) (A ⧸ J) f ∈ maximalIdeal (A ⧸ J) := by
      rw [← hkerC, RingHom.mem_ker, hcompC]
      exact hfm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hf
  haveI hcplC : IsAdicComplete (maximalIdeal (A ⧸ J)) (A ⧸ J) :=
    IsLocalRing.isAdicComplete_of_module_finite (𝒪 := PowerSeries W₀)

  set π : A →+* A ⧸ J := Ideal.Quotient.mk J with hπdef
  set Gc : FormalGroup (A ⧸ J) := Fu.map (algebraMap (PowerSeries W₀) (A ⧸ J)) with hGcdef
  have hGc : Fu.IsBaseChange (algebraMap (PowerSeries W₀) (A ⧸ J)) Gc := rfl
  have hGac : Ga.IsBaseChange π Gc := by
    show Gc.toPowerSeries = MvPowerSeries.map π Ga.toPowerSeries
    rw [hGcdef, hGadef, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map]
    rfl
  have hπx₀ : π x₀ ∈ maximalIdeal (A ⧸ J) := by
    rw [← hkerC, RingHom.mem_ker, hπdef, hresCdef, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hkerA]; exact hx₀
  have hπx₁ : π x₁ ∈ maximalIdeal (A ⧸ J) := by
    rw [← hkerC, RingHom.mem_ker, hπdef, hresCdef, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hkerA]; exact hx₁

  have hfacC : Gc.nthSeries q = ((P.map (algebraMap (PowerSeries W₀) (A ⧸ J)) : (A ⧸ J)[X]) : PowerSeries (A ⧸ J)) *
      PowerSeries.map (algebraMap (PowerSeries W₀) (A ⧸ J)) U := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fu _ Gc hGc q, hfac, map_mul, Polynomial.polynomial_map_coe]

  have hDC : R4aP.dpoly Gc (maximalIdeal (A ⧸ J)) q (π x₀) (π x₁) = P.map (algebraMap (PowerSeries W₀) (A ⧸ J)) := by
    rw [← R4aP.dpoly_map (maximalIdeal A) (maximalIdeal (A ⧸ J)) π Ga Gc hGac q x₀ x₁ hx₀ hx₁ hπx₀ hπx₁]
    have h1 : (DA - PA).map π = 0 := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, hπdef, Ideal.Quotient.eq_zero_iff_mem, hJdef]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [Polynomial.map_sub, sub_eq_zero] at h1
    rw [← hDAdef, h1, hPAdef, Polynomial.map_map]
    rfl
  have hDrin : Gc.IsDrinfeldBasisAdic (maximalIdeal (A ⧸ J)) q (π x₀) (π x₁) :=
    (R4aE.isDrinfeldBasisAdic_iff_dpoly_eq Gc q _ _
      (hPmonic.map _) (by rw [hPmonic.natDegree_map, hPdeg]) (hU.map _) hfacC (π x₀) (π x₁) hπx₀ hπx₁).mpr hDC
  refine ⟨A ⧸ J, inferInstance, inferInstance, hlocC, hfinC, hcplC, resC, hresC, hkerC, hcompC, Gc, hGc,
    π x₀, π x₁, hπx₀, hπx₁, hDrin, ?_⟩

  intro B _ _ _ _ G hG y₀ y₁ hy₀ hy₁ hD

  have hfacB : G.nthSeries q = ((P.map (algebraMap (PowerSeries W₀) B) : B[X]) : PowerSeries B) *
      PowerSeries.map (algebraMap (PowerSeries W₀) B) U := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fu _ G hG q, hfac, map_mul, Polynomial.polynomial_map_coe]
  have hDB : R4aP.dpoly G (maximalIdeal B) q y₀ y₁ = P.map (algebraMap (PowerSeries W₀) B) :=
    (R4aE.isDrinfeldBasisAdic_iff_dpoly_eq G q _ _
      (hPmonic.map _) (by rw [hPmonic.natDegree_map, hPdeg]) (hU.map _) hfacB y₀ y₁ hy₀ hy₁).mp hD
  obtain ⟨hev₀, hev₁⟩ :=
    FormalGroup.IsDrinfeldBasisAdic.evalSeries_nthSeries_eq_zero (maximalIdeal B) G q hq2 y₀ y₁ hy₀ hy₁ hD
  have hPy₀ : aeval y₀ P = 0 := R4aP.aeval_eq_zero_of_evalSeries_eq_zero G q P U hU hfacB y₀ hy₀ hev₀
  have hPy₁ : aeval y₁ P = 0 := R4aP.aeval_eq_zero_of_evalSeries_eq_zero G q P U hU hfacB y₁ hy₁ hev₁

  obtain ⟨χA, ⟨hχA₀, hχA₁⟩, hχAuniq⟩ := huniv B y₀ y₁ hPy₀ hPy₁
  have hGab : Ga.IsBaseChange (χA : A →+* B) G := by
    show G.toPowerSeries = MvPowerSeries.map (χA : A →+* B) Ga.toPowerSeries
    rw [hG, hGadef, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map, χA.comp_algebraMap]
  have hχy₀ : (χA : A →+* B) x₀ ∈ maximalIdeal B := by rw [AlgHom.coe_toRingHom, hχA₀]; exact hy₀
  have hχy₁ : (χA : A →+* B) x₁ ∈ maximalIdeal B := by rw [AlgHom.coe_toRingHom, hχA₁]; exact hy₁
  have hDAB : DA.map (χA : A →+* B) = PA.map (χA : A →+* B) := by
    rw [hDAdef, R4aP.dpoly_map (maximalIdeal A) (maximalIdeal B) (χA : A →+* B) Ga G hGab q x₀ x₁ hx₀ hx₁ hχy₀ hχy₁,
      AlgHom.coe_toRingHom, hχA₀, hχA₁, hDB, hPAdef, Polynomial.map_map]
    congr 1
    exact (χA.comp_algebraMap).symm
  have hJχ : ∀ a ∈ J, χA a = 0 := by
    intro a ha
    have hle : J ≤ RingHom.ker (χA : A →+* B) := by
      rw [hJdef, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, ← Polynomial.coeff_map, Polynomial.map_sub, hDAB, sub_self,
        Polynomial.coeff_zero]
    exact hle ha
  have hmk : ∀ a : A, Ideal.Quotient.mkₐ (PowerSeries W₀) J a = π a := fun a => rfl
  refine ⟨Ideal.Quotient.liftₐ J χA hJχ, ⟨?_, ?_⟩, ?_⟩
  · show Ideal.Quotient.liftₐ J χA hJχ (Ideal.Quotient.mk J x₀) = y₀
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; exact hχA₀
  · show Ideal.Quotient.liftₐ J χA hJχ (Ideal.Quotient.mk J x₁) = y₁
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; exact hχA₁
  · rintro χ' ⟨h0', h1'⟩
    apply Ideal.Quotient.algHom_ext
    have e1 : χ'.comp (Ideal.Quotient.mkₐ (PowerSeries W₀) J) = χA :=
      hχAuniq _ ⟨by rw [AlgHom.comp_apply, hmk]; exact h0', by rw [AlgHom.comp_apply, hmk]; exact h1'⟩
    have e2 : (Ideal.Quotient.liftₐ J χA hJχ).comp (Ideal.Quotient.mkₐ (PowerSeries W₀) J) = χA :=
      hχAuniq _ ⟨by rw [AlgHom.comp_apply, hmk, hπdef, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; exact hχA₀,
        by rw [AlgHom.comp_apply, hmk, hπdef, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; exact hχA₁⟩
    exact e1.trans e2.symm

end PartP

end S_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_moduleFinite_isLocalRing_represents_isDrinfeldBasisAdic (solution)

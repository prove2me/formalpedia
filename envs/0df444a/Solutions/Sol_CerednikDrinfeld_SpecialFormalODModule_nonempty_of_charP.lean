-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/58b49bd9-8791-56f6-a02b-dcaff5eb53dd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_WittVector_existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
import Theorems.Thm_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_X_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace P2mKcSFMExists

variable {p : ℕ} [Fact p.Prime]

scoped instance instFintypeGF : Fintype (GaloisField p 2) := Fintype.ofFinite _

theorem card_GF : Fintype.card (GaloisField p 2) = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card p 2 two_ne_zero]

theorem two_le_card : 2 ≤ Fintype.card (GaloisField p 2) := Fintype.one_lt_card

local notation "𝕆" => Zp2 p
local notation "𝔮" => Fintype.card (GaloisField p 2)

theorem frobenius_frobenius (a : 𝕆) : WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← sq,
    ← card_GF, FiniteField.pow_card]

theorem exists_pow_ne : ∃ ω : GaloisField p 2, ω ^ p ≠ ω := by
  classical
  by_contra h
  push Not at h
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set P : Polynomial (GaloisField p 2) := Polynomial.X ^ p - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1
  have hroots : ∀ ω : GaloisField p 2, ω ∈ P.roots := by
    intro ω
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h ω, sub_self]
  have hcard : Fintype.card (GaloisField p 2) ≤ p := by
    calc Fintype.card (GaloisField p 2) = (Finset.univ : Finset (GaloisField p 2)).card :=
          Finset.card_univ.symm
      _ ≤ P.roots.toFinset.card :=
          Finset.card_le_card fun ω _ => Multiset.mem_toFinset.mpr (hroots ω)
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = p := hdeg
  rw [card_GF, sq] at hcard
  have : p * p ≤ p * 1 := by simpa using hcard
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem exists_isUnit_frobenius_sub : ∃ a : 𝕆, IsUnit (WittVector.frobenius a - a) := by
  obtain ⟨ω, hω⟩ := exists_pow_ne (p := p)
  refine ⟨WittVector.teichmuller p ω, WittVector.isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr hω

variable (p)

def fvec (τ : Type*) : τ → MvPowerSeries τ 𝕆 :=
  fun s => C (p : 𝕆) * X s + X s ^ 𝔮

def Comm {τ : Type*} (φ : MvPowerSeries τ 𝕆) : Prop :=
  C (p : 𝕆) * φ + φ ^ 𝔮 = subst (fvec p τ) φ

theorem lt_existsUnique (τ : Type*) [Finite τ] (c : τ → 𝕆) :
    ∃! φ : MvPowerSeries τ 𝕆, constantCoeff φ = 0 ∧
      (∀ s, coeff (Finsupp.single s 1) φ = c s) ∧ Comm p φ :=
  WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst p
    (GaloisField p 2) τ c

def lt (τ : Type*) [Finite τ] (c : τ → 𝕆) : MvPowerSeries τ 𝕆 :=
  (lt_existsUnique p τ c).exists.choose

variable {p}

section LT

variable {τ : Type*}

theorem lt_spec [Finite τ] (c : τ → 𝕆) :
    constantCoeff (lt p τ c) = 0 ∧ (∀ s, coeff (Finsupp.single s 1) (lt p τ c) = c s) ∧
      Comm p (lt p τ c) :=
  (lt_existsUnique p τ c).exists.choose_spec

theorem constantCoeff_lt [Finite τ] (c : τ → 𝕆) : constantCoeff (lt p τ c) = 0 := (lt_spec c).1

theorem coeff_single_lt [Finite τ] (c : τ → 𝕆) (s : τ) :
    coeff (Finsupp.single s 1) (lt p τ c) = c s := (lt_spec c).2.1 s

theorem comm_lt [Finite τ] (c : τ → 𝕆) : Comm p (lt p τ c) := (lt_spec c).2.2

theorem eq_of_comm [Finite τ] {φ ψ : MvPowerSeries τ 𝕆}
    (hφ0 : constantCoeff φ = 0) (hψ0 : constantCoeff ψ = 0) (hφ : Comm p φ) (hψ : Comm p ψ)
    (h1 : ∀ s, coeff (Finsupp.single s 1) φ = coeff (Finsupp.single s 1) ψ) : φ = ψ :=
  (lt_existsUnique p τ fun s => coeff (Finsupp.single s 1) ψ).unique ⟨hφ0, h1, hφ⟩
    ⟨hψ0, fun _ => rfl, hψ⟩

theorem constantCoeff_fvec (s : τ) : constantCoeff (fvec p τ s) = 0 := by
  have h0 : 𝔮 ≠ 0 := by have := two_le_card (p := p); omega
  simp only [fvec, map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, map_pow,
    zero_pow h0, add_zero]

theorem hasSubst_fvec [Finite τ] : HasSubst (fvec p τ) :=
  hasSubst_of_constantCoeff_zero constantCoeff_fvec

theorem coeff_single_X_pow_card [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) ((X s : MvPowerSeries τ 𝕆) ^ 𝔮) = 0 := by
  rw [coeff_X_pow, if_neg]
  intro h
  have := congrArg (fun d => d t) h
  simp only [Finsupp.single_eq_same] at this
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same] at this
    have := two_le_card (p := p)
    omega
  · rw [Finsupp.single_eq_of_ne hts] at this
    exact one_ne_zero this

theorem coeff_single_fvec [DecidableEq τ] (s t : τ) :
    coeff (Finsupp.single t 1) (fvec p τ s) = if t = s then (p : 𝕆) else 0 := by
  rw [fvec, map_add, coeff_C_mul, coeff_index_single_X, coeff_single_X_pow_card, add_zero]
  split_ifs <;> simp

theorem comm_X [Finite τ] (s : τ) : Comm p (X s : MvPowerSeries τ 𝕆) := by
  unfold Comm
  rw [subst_X hasSubst_fvec]
  rfl

theorem comm_fvec [Finite τ] (s : τ) : Comm p (fvec p τ s) := by
  have hf : HasSubst (fvec p τ) := hasSubst_fvec
  unfold Comm
  conv_rhs => rw [fvec]
  rw [subst_add hf, subst_mul hf, subst_C, subst_pow hf, subst_X hf]

theorem comm_subst {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) {a : σ → MvPowerSeries τ 𝕆}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, Comm p (a s)) :
    Comm p (subst a φ) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  unfold Comm at *
  calc C (p : 𝕆) * subst a φ + subst a φ ^ 𝔮
      = subst a (C (p : 𝕆) * φ + φ ^ 𝔮) := by
        rw [subst_add hsa, subst_mul hsa, subst_pow hsa, subst_C]
    _ = subst a (subst (fvec p σ) φ) := by rw [hφ]
    _ = subst (fun s => subst a (fvec p σ s)) φ :=
        subst_comp_subst_apply hasSubst_fvec hsa φ
    _ = subst (fun s => subst (fvec p τ) (a s)) φ := by
        congr 1
        funext s
        show subst a (C (p : 𝕆) * X s + X s ^ 𝔮) = _
        rw [subst_add hsa, subst_mul hsa, subst_C, subst_pow hsa, subst_X hsa]
        exact ha s
    _ = subst (fvec p τ) (subst a φ) := (subst_comp_subst_apply hsa hasSubst_fvec φ).symm

theorem comm_subst_X {σ : Type*} [Finite σ] [Finite τ] {φ : MvPowerSeries σ 𝕆}
    (hφ : Comm p φ) (e : σ → τ) :
    Comm p (subst (fun s => (X (e s) : MvPowerSeries τ 𝕆)) φ) :=
  comm_subst hφ (fun _ => constantCoeff_X _) fun _ => comm_X _

theorem constantCoeff_subst_of {σ : Type*} [Finite σ] {φ : MvPowerSeries σ 𝕆}
    (hφ : constantCoeff φ = 0) {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) :
    constantCoeff (subst a φ) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha0) ha0 hφ

theorem coeff_single_subst_lt {σ : Type*} [Fintype σ] [Fintype τ] (c : σ → 𝕆)
    {a : σ → MvPowerSeries τ 𝕆} (ha0 : ∀ s, constantCoeff (a s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (lt p σ c)) = ∑ s, c s * coeff (Finsupp.single t 1) (a s) := by
  rw [MvFormalGroup.coeff_single_subst ha0]
  simp only [coeff_single_lt]

end LT

section Standard

def lawLin (i : Fin 2) : Fin 2 ⊕ Fin 2 → 𝕆 :=
  Sum.elim (fun j => if j = i then 1 else 0) (fun j => if j = i then 1 else 0)

theorem sum_lawLin_mul (i : Fin 2) (g : Fin 2 ⊕ Fin 2 → 𝕆) :
    ∑ v, lawLin (p := p) i v * g v = g (Sum.inl i) + g (Sum.inr i) := by
  rw [Fintype.sum_sum_type]
  simp only [lawLin, Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lawLin_eq (i : Fin 2) (v : Fin 2 ⊕ Fin 2) :
    lawLin (p := p) i v = (if v = Sum.inl i then 1 else 0) + (if v = Sum.inr i then 1 else 0) := by
  rcases v with j | j <;> by_cases h : j = i <;> simp [lawLin, h]

variable (p)

def lawSeries (i : Fin 2) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆 := lt p (Fin 2 ⊕ Fin 2) (lawLin i)

variable {p}

theorem constantCoeff_lawSeries (i : Fin 2) : constantCoeff (lawSeries p i) = 0 := constantCoeff_lt _

theorem comm_lawSeries (i : Fin 2) : Comm p (lawSeries p i) := comm_lt _

theorem coeff_single_lawSeries (i : Fin 2) (v : Fin 2 ⊕ Fin 2) :
    coeff (Finsupp.single v 1) (lawSeries p i)
      = (if v = Sum.inl i then 1 else 0) + (if v = Sum.inr i then 1 else 0) := by
  rw [lawSeries, coeff_single_lt, lawLin_eq]

theorem coeff_single_subst_lawSeries {τ : Type*} [Fintype τ] (i : Fin 2)
    {a : Fin 2 ⊕ Fin 2 → MvPowerSeries τ 𝕆} (ha0 : ∀ v, constantCoeff (a v) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a (lawSeries p i))
      = coeff (Finsupp.single t 1) (a (Sum.inl i)) + coeff (Finsupp.single t 1) (a (Sum.inr i)) := by
  rw [lawSeries, coeff_single_subst_lt _ ha0, sum_lawLin_mul]

def law : MvFormalGroup 2 𝕆 where
  toPowerSeries := lawSeries p
  constantCoeff_eq_zero := constantCoeff_lawSeries
  coeff_single_inl i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  coeff_single_inr i j := by
    rw [coeff_single_lawSeries]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  assoc i := by
    classical

    have hB : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hC : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) s) = 0 := by
      rintro (l | l) <;> exact constantCoeff_X _
    have hBv : (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inl l))) = fun s => X (Sum.elim (fun l => Sum.inl l)
          (fun l => Sum.inr (Sum.inl l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hCv : (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun l => X (Sum.inr (Sum.inr l))) = fun s => X (Sum.elim (fun l => Sum.inr (Sum.inl l))
          (fun l => Sum.inr (Sum.inr l)) s) := by
      funext s; rcases s with l | l <;> rfl
    have hA : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
          fun l => X (Sum.inr (Sum.inl l))) (lawSeries p j))
        fun j => X (Sum.inr (Sum.inr j))) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_subst_of (constantCoeff_lawSeries j) hB
      · exact constantCoeff_X _
    have hA' : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) 𝕆))
          fun l => X (Sum.inr (Sum.inr l))) (lawSeries p j)) s) = 0 := by
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_of (constantCoeff_lawSeries j) hC
    refine eq_of_comm (constantCoeff_subst_of (constantCoeff_lawSeries i) hA)
      (constantCoeff_subst_of (constantCoeff_lawSeries i) hA') ?_ ?_ ?_
    · refine comm_subst (comm_lawSeries i) hA ?_
      rintro (j | j)
      · show Comm p (subst _ (lawSeries p j))
        rw [hBv]
        exact comm_subst_X (comm_lawSeries j) _
      · exact comm_X _
    · refine comm_subst (comm_lawSeries i) hA' ?_
      rintro (j | j)
      · exact comm_X _
      · show Comm p (subst _ (lawSeries p j))
        rw [hCv]
        exact comm_subst_X (comm_lawSeries j) _
    · intro t
      rw [coeff_single_subst_lawSeries i hA, coeff_single_subst_lawSeries i hA']
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [coeff_single_subst_lawSeries i hB, coeff_single_subst_lawSeries i hC]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact add_assoc _ _ _

scoped instance law_isComm : (law (p := p)).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (lawSeries p i) = lawSeries p i
    refine eq_of_comm (constantCoeff_subst_of (constantCoeff_lawSeries i) hS)
      (constantCoeff_lawSeries i) ?_ (comm_lawSeries i) ?_
    · rw [hSv]
      exact comm_subst_X (comm_lawSeries i) _
    · intro t
      rw [coeff_single_subst_lawSeries i hS, coeff_single_lawSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      exact add_comm _ _

def chi (i : Fin 2) : 𝕆 →+* 𝕆 := if i = 0 then RingHom.id _ else WittVector.frobenius

@[scoped simp] theorem chi_zero : chi (p := p) 0 = RingHom.id _ := rfl

@[scoped simp] theorem chi_one : chi (p := p) 1 = WittVector.frobenius := rfl

theorem chi_frobenius (i : Fin 2) (a : 𝕆) :
    chi i (WittVector.frobenius a) = WittVector.frobenius (chi i a) := by
  fin_cases i <;> simp

theorem chi_natCast (i : Fin 2) : chi i (p : 𝕆) = p := map_natCast _ _

variable (p)

def actSeries (a : 𝕆) : Series 𝕆 := fun i => lt p (Fin 2) fun s => if s = i then chi i a else 0

def varpiLin (i s : Fin 2) : 𝕆 := if i = 0 then (if s = 1 then p else 0) else (if s = 0 then 1 else 0)

def varpiSeries : Series 𝕆 := fun i => lt p (Fin 2) (varpiLin p i)

variable {p}

theorem constantCoeff_actSeries (a : 𝕆) (i : Fin 2) : constantCoeff (actSeries p a i) = 0 :=
  constantCoeff_lt _

theorem comm_actSeries (a : 𝕆) (i : Fin 2) : Comm p (actSeries p a i) := comm_lt _

theorem coeff_single_actSeries (a : 𝕆) (i s : Fin 2) :
    coeff (Finsupp.single s 1) (actSeries p a i) = if s = i then chi i a else 0 := by
  rw [actSeries, coeff_single_lt]

theorem coeff_single_subst_actSeries {τ : Type*} [Fintype τ] (a : 𝕆) (i : Fin 2)
    {b : Fin 2 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (actSeries p a i))
      = chi i a * coeff (Finsupp.single t 1) (b i) := by
  rw [actSeries, coeff_single_subst_lt _ hb0]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem constantCoeff_varpiSeries (i : Fin 2) : constantCoeff (varpiSeries p i) = 0 :=
  constantCoeff_lt _

theorem comm_varpiSeries (i : Fin 2) : Comm p (varpiSeries p i) := comm_lt _

theorem coeff_single_varpiSeries (i s : Fin 2) :
    coeff (Finsupp.single s 1) (varpiSeries p i) = varpiLin p i s := by
  rw [varpiSeries, coeff_single_lt]

theorem sum_varpiLin_mul (i : Fin 2) (g : Fin 2 → 𝕆) :
    ∑ s, varpiLin p i s * g s = if i = 0 then (p : 𝕆) * g 1 else g 0 := by
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp [varpiLin]

theorem coeff_single_subst_varpiSeries {τ : Type*} [Fintype τ] (i : Fin 2)
    {b : Fin 2 → MvPowerSeries τ 𝕆} (hb0 : ∀ s, constantCoeff (b s) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst b (varpiSeries p i))
      = if i = 0 then (p : 𝕆) * coeff (Finsupp.single t 1) (b 1)
        else coeff (Finsupp.single t 1) (b 0) := by
  rw [varpiSeries, coeff_single_subst_lt _ hb0, sum_varpiLin_mul]

theorem constantCoeff_homFamily {φ : Series 𝕆} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆)) (φ j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆)) (φ j)) s) = 0 := by
  rintro (j | j) <;> exact constantCoeff_subst_of (hφ j) (fun l => constantCoeff_X _)

theorem isLawHom_of_comm {φ : Series 𝕆} (h0 : ∀ i, constantCoeff (φ i) = 0)
    (hc : ∀ i, Comm p (φ i)) : IsLawHom (law (p := p)) law φ := by
  classical
  refine ⟨h0, fun i => ?_⟩
  have hF : ∀ j, constantCoeff (lawSeries p j) = 0 := constantCoeff_lawSeries
  have hA := constantCoeff_homFamily h0
  refine eq_of_comm (constantCoeff_subst_of (h0 i) hF)
    (constantCoeff_subst_of (constantCoeff_lawSeries i) hA)
    (comm_subst (hc i) hF comm_lawSeries) (comm_subst (comm_lawSeries i) hA ?_) ?_
  · rintro (j | j) <;> exact comm_subst_X (hc j) _
  · intro t
    show coeff _ (subst (lawSeries p) (φ i)) = coeff _ (subst _ (lawSeries p i))
    rw [coeff_single_subst_lawSeries i hA, MvFormalGroup.coeff_single_subst hF]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_lawSeries]
    rw [MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _),
      MvFormalGroup.coeff_single_subst (fun l => constantCoeff_X _)]
    simp only [coeff_index_single_X, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]

def standard : FormalODModule p 𝕆 where
  F := law
  isComm := law_isComm
  act := actSeries p
  varpi := varpiSeries p
  isLawHom_act a := isLawHom_of_comm (constantCoeff_actSeries a) (comm_actSeries a)
  isLawHom_varpi := isLawHom_of_comm constantCoeff_varpiSeries comm_varpiSeries
  act_one := by
    classical
    funext i
    refine eq_of_comm (constantCoeff_actSeries 1 i) (constantCoeff_X i) (comm_actSeries 1 i)
      (comm_X i) fun s => ?_
    rw [coeff_single_actSeries, map_one]
    exact (coeff_index_single_X i s).symm
  act_mul a b := by
    classical
    funext i
    refine eq_of_comm (constantCoeff_actSeries _ i)
      (constantCoeff_subst_of (constantCoeff_actSeries a i) (constantCoeff_actSeries b))
      (comm_actSeries _ i) (comm_subst (comm_actSeries a i) (constantCoeff_actSeries b)
        (comm_actSeries b)) fun s => ?_
    show _ = coeff _ (subst (actSeries p b) (actSeries p a i))
    rw [coeff_single_actSeries, coeff_single_subst_actSeries a i (constantCoeff_actSeries b),
      coeff_single_actSeries, map_mul]
    split_ifs <;> ring
  act_add a b := by
    classical
    funext i
    have hab : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim (actSeries p a) (actSeries p b)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_actSeries _ j
    refine eq_of_comm (constantCoeff_actSeries _ i)
      (constantCoeff_subst_of (constantCoeff_lawSeries i) hab)
      (comm_actSeries _ i) (comm_subst (comm_lawSeries i) hab ?_) fun s => ?_
    · rintro (j | j) <;> exact comm_actSeries _ j
    · show _ = coeff _ (subst _ (lawSeries p i))
      rw [coeff_single_actSeries, coeff_single_subst_lawSeries i hab]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_single_actSeries, map_add]
      split_ifs <;> ring
  varpi_comp_varpi := by
    classical
    funext i
    refine eq_of_comm
      (constantCoeff_subst_of (constantCoeff_varpiSeries i) constantCoeff_varpiSeries)
      (constantCoeff_actSeries _ i)
      (comm_subst (comm_varpiSeries i) constantCoeff_varpiSeries comm_varpiSeries)
      (comm_actSeries _ i) fun s => ?_
    show coeff _ (subst (varpiSeries p) (varpiSeries p i)) = _
    rw [coeff_single_subst_varpiSeries i constantCoeff_varpiSeries, coeff_single_varpiSeries,
      coeff_single_varpiSeries, coeff_single_actSeries, chi_natCast]
    fin_cases i <;> fin_cases s <;> simp [varpiLin]
  varpi_comp_act a := by
    classical
    funext i
    refine eq_of_comm
      (constantCoeff_subst_of (constantCoeff_varpiSeries i) (constantCoeff_actSeries a))
      (constantCoeff_subst_of (constantCoeff_actSeries _ i) constantCoeff_varpiSeries)
      (comm_subst (comm_varpiSeries i) (constantCoeff_actSeries a) (comm_actSeries a))
      (comm_subst (comm_actSeries _ i) constantCoeff_varpiSeries comm_varpiSeries) fun s => ?_
    show coeff _ (subst (actSeries p a) (varpiSeries p i))
      = coeff _ (subst (varpiSeries p) (actSeries p _ i))
    rw [coeff_single_subst_varpiSeries i (constantCoeff_actSeries a), coeff_single_actSeries,
      coeff_single_actSeries, coeff_single_subst_actSeries _ i constantCoeff_varpiSeries,
      coeff_single_varpiSeries]
    fin_cases i <;> fin_cases s <;> simp [varpiLin, frobenius_frobenius, mul_comm]

theorem standard_act_p : (standard (p := p)).act (p : 𝕆) = fvec p (Fin 2) := by
  classical
  funext i
  refine eq_of_comm (constantCoeff_actSeries _ i) (constantCoeff_fvec i) (comm_actSeries _ i)
    (comm_fvec i) fun s => ?_
  show coeff _ (actSeries p _ i) = _
  rw [coeff_single_actSeries, coeff_single_fvec, chi_natCast]

theorem coeff_single_standard_act (a : 𝕆) (i s : Fin 2) :
    coeff (Finsupp.single s 1) ((standard (p := p)).act a i) = if s = i then chi i a else 0 :=
  coeff_single_actSeries a i s

end Standard

section OverB

variable {B : Type*} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

def modB : FormalODModule p B := (standard (p := p)).map j

theorem lieAct_apply (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (modB j).lieAct a m i = j (chi i a) * m i := by
  classical
  show (Matrix.mulVecLin (MvFormalGroup.linearPart ((modB j).act a))) m i = _
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [MvFormalGroup.linearPart, Matrix.of_apply]
  show ∑ s, coeff (Finsupp.single s 1) (MvPowerSeries.map j ((standard (p := p)).act a i)) * m s = _
  simp only [MvPowerSeries.coeff_map, coeff_single_standard_act, apply_ite j, map_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sub_smul_apply (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (((modB j).lieAct a - j a • (LinearMap.id : (modB j).Lie →ₗ[B] (modB j).Lie)) m) i
      = (j (chi i a) - j a) * m i := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply,
    Pi.smul_apply, lieAct_apply, smul_eq_mul, sub_mul]

theorem sub_smul_apply' (a : 𝕆) (m : (modB j).Lie) (i : Fin 2) :
    (((modB j).lieAct a - j (WittVector.frobenius a) •
        (LinearMap.id : (modB j).Lie →ₗ[B] (modB j).Lie)) m) i
      = (j (chi i a) - j (WittVector.frobenius a)) * m i := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply,
    Pi.smul_apply, lieAct_apply, smul_eq_mul, sub_mul]

theorem mem_lieZero_iff (m : (modB j).Lie) : m ∈ (modB j).lieZero j ↔ m 1 = 0 := by
  rw [FormalODModule.lieZero, Submodule.mem_iInf]
  constructor
  · intro h
    obtain ⟨a₀, ha₀⟩ := exists_isUnit_frobenius_sub (p := p)
    have h1 := congrFun (LinearMap.mem_ker.mp (h a₀)) 1
    rw [sub_smul_apply, Pi.zero_apply, chi_one, ← map_sub] at h1
    exact (ha₀.map j).mul_right_eq_zero.mp h1
  · intro hm a
    rw [LinearMap.mem_ker]
    funext i
    rw [sub_smul_apply, Pi.zero_apply]
    fin_cases i
    · simp
    · simp [hm]

theorem mem_lieOne_iff (m : (modB j).Lie) : m ∈ (modB j).lieOne j ↔ m 0 = 0 := by
  rw [FormalODModule.lieOne, Submodule.mem_iInf]
  constructor
  · intro h
    obtain ⟨a₀, ha₀⟩ := exists_isUnit_frobenius_sub (p := p)
    have h1 := congrFun (LinearMap.mem_ker.mp (h a₀)) 0
    rw [sub_smul_apply', Pi.zero_apply, chi_zero, RingHom.id_apply, ← map_sub] at h1
    have hu : IsUnit (a₀ - WittVector.frobenius a₀) := by
      rw [← neg_sub]
      exact ha₀.neg
    exact (hu.map j).mul_right_eq_zero.mp h1
  · intro hm a
    rw [LinearMap.mem_ker]
    funext i
    rw [sub_smul_apply', Pi.zero_apply]
    fin_cases i
    · simp [hm]
    · simp

theorem isCompl_lie : IsCompl ((modB j).lieZero j) ((modB j).lieOne j) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [Submodule.eq_bot_iff]
    intro m hm
    rw [Submodule.mem_inf, mem_lieZero_iff, mem_lieOne_iff] at hm
    funext i
    fin_cases i
    · exact hm.2
    · exact hm.1
  · rw [Submodule.eq_top_iff']
    intro m
    rw [Submodule.mem_sup]
    refine ⟨Pi.single 0 (m 0), (mem_lieZero_iff j _).mpr (by simp), Pi.single 1 (m 1),
      (mem_lieOne_iff j _).mpr (by simp), ?_⟩
    funext i
    fin_cases i <;> simp

def lieZeroEquiv : ↥((modB j).lieZero j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 0 b, (mem_lieZero_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simp
    · simpa using ((mem_lieZero_iff j _).mp m.2).symm
  right_inv b := by simp

def lieOneEquiv : ↥((modB j).lieOne j) ≃ₗ[B] B where
  toFun m := (m : Fin 2 → B) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨Pi.single 1 b, (mem_lieOne_iff j _).mpr (by simp)⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    fin_cases i
    · simpa using ((mem_lieOne_iff j _).mp m.2).symm
    · simp
  right_inv b := by simp

theorem isSpecial : (modB j).IsSpecial j :=
  ⟨isCompl_lie j, Module.Invertible.congr (lieZeroEquiv j).symm,
    Module.Invertible.congr (lieOneEquiv j).symm⟩

theorem modB_act_p : (modB j).act (p : 𝕆) = fun i => (X i : MvPowerSeries (Fin 2) B) ^ 𝔮 := by
  show ((standard (p := p)).act (p : 𝕆)).map j = _
  rw [standard_act_p]
  funext i
  show MvPowerSeries.map j (C (p : 𝕆) * X i + X i ^ 𝔮) = X i ^ 𝔮
  rw [map_add, map_mul, map_C, map_natCast, CharP.cast_eq_zero, map_zero, zero_mul, zero_add,
    map_pow, map_X]

theorem hasKernelOfDegree_X_pow :
    FormalODModule.HasKernelOfDegree (fun i => (X i : MvPowerSeries (Fin 2) B) ^ 𝔮) (p ^ 4) := by
  haveI : Nontrivial B := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  obtain ⟨hfree, hfin, -⟩ :=
    MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow B 2 (fun _ => 𝔮)
  refine ⟨hfin, Module.Projective.of_free, fun κ _ f => ?_⟩
  have hφ : (fun i : Fin 2 => MvPowerSeries.map f ((X i : MvPowerSeries (Fin 2) B) ^ 𝔮))
      = fun i => (X i : MvPowerSeries (Fin 2) κ) ^ 𝔮 := by
    funext i
    rw [map_pow, map_X]
  show Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range
    fun i : Fin 2 => MvPowerSeries.map f ((X i : MvPowerSeries (Fin 2) B) ^ 𝔮))) = p ^ 4
  rw [hφ, (MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_X_pow κ 2 fun _ => 𝔮).2.2,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_GF, ← pow_mul]

theorem hasHeight : (modB j).HasHeight 4 := by
  show FormalODModule.HasKernelOfDegree ((modB j).act (p : 𝕆)) (p ^ 4)
  rw [modB_act_p]
  exact hasKernelOfDegree_X_pow

end OverB

end P2mKcSFMExists
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP.P2mKcSFMExists"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP.P2mKcSFMExists"

universe u in
theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) :
    Nonempty (CerednikDrinfeld.SpecialFormalODModule p j) :=
  ⟨{ toFormalODModule := P2mKcSFMExists.modB j
     isSpecial := P2mKcSFMExists.isSpecial j
     hasHeight := P2mKcSFMExists.hasHeight j }⟩

end S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP (solution)

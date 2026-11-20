-- Prove2me | solution 2 for DeletionHash.MixedEdit.odd_cycles_rare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:24.277975+00:00
-- url     : https://prove2.me/submissions/81bd771b-801c-48eb-8f50-5743afb782b4

import Mathlib
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
import Theorems.Thm_DeletionHash_MixedEdit_count_generating_sets
import Theorems.Thm_DeletionHash_MixedEdit_bounded_witness
import Theorems.Thm_DeletionHash_MixedEdit_independent_differences

namespace DeletionGraph.ExceptionalProbability
open DeletionHash.MixedEdit
universe u v

theorem probability_mono {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ x, P x → Q x) : uniformProbability P ≤ uniformProbability Q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {x // P x} => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
    (fun x y he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))

theorem probability_union {Ω : Type u} [Fintype Ω] {β : Type v}
    (S : Finset β) (P : β → Ω → Prop) :
    uniformProbability (fun x => ∃ z ∈ S, P z x) ≤ ∑ z ∈ S, uniformProbability (P z) := by
  classical
  let E : β → Finset Ω := fun z => Finset.univ.filter (P z)
  have he : Finset.univ.filter (fun x => ∃ z ∈ S, P z x) = S.biUnion E := by
    ext x
    simp [E]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he]
  have hc : (S.biUnion E).card ≤ ∑ z ∈ S, (E z).card := Finset.card_biUnion_le
  calc
    ((S.biUnion E).card : ℝ) / Fintype.card Ω ≤
        ((∑ z ∈ S, (E z).card : ℕ) : ℝ) / Fintype.card Ω := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hc
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_div, E]

end DeletionGraph.ExceptionalProbability

namespace DeletionGraph.ExponentAbsorption
open DeletionHash.MixedEdit

theorem witness_le_cube (t b L : ℕ) (hL : 1+4*t+4*t*b ≤ L) :
    witnessBound t b L ≤ L^3 := by
  have hL1 : 1 ≤ L := by omega
  have hb : 2*L+2*b-2 ≤ 2*L+2*b := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left (2*t) hb
  have hm' := Nat.mul_le_mul_right L hm
  have hLsq : 1 ≤ L^2 := one_le_pow₀ hL1
  have hconst : (1+4*t+4*t*b)*L^2 ≤ L^3 := by
    calc
      _ ≤ L*L^2 := Nat.mul_le_mul_right _ hL
      _ = L^3 := by ring
  have hterm : 4*t*b*L ≤ 4*t*b*L^2 := by
    apply Nat.mul_le_mul_left
    nlinarith
  unfold witnessBound
  nlinarith [hm',hconst,hterm]

theorem exponent_bound (t b a L : ℕ) (hL : 1+4*t+4*t*b ≤ L) :
    ExponentBound t b a (4*a+2) L := by
  intro R hR hRmax
  have hL1 : 1 ≤ L := by omega
  have hRc : R ≤ L^3 := hRmax.trans (witness_le_cube t b L hL)
  have hpoly : 2*t*R+1 ≤ L^4 := by
    have h1 : 2*t*R+1 ≤ (2*t+1)*R := by nlinarith
    have h2 : (2*t+1)*R ≤ L*L^3 :=
      Nat.mul_le_mul (by omega) hRc
    have he : L*L^3=L^4 := by ring
    omega
  have hpow : L^4 ≤ L^(2*R) := by
    exact Nat.pow_le_pow_right hL1 (by omega)
  have hbase : L*R ≤ L^4 := by
    calc
      _ ≤ L*L^3 := Nat.mul_le_mul_left L hRc
      _ = L^4 := by ring
  calc
    (2*t*R+1)*(L*R)^(a*R) ≤ L^(2*R)*(L^4)^(a*R) :=
      Nat.mul_le_mul (hpoly.trans hpow) (Nat.pow_le_pow_left hbase _)
    _ = L^((4*a+2)*R) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring

theorem eventual (t b a : ℕ) :
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L := by
  exact ⟨4*a+2,1+4*t+4*t*b,by omega,by omega,
    fun L hL => exponent_bound t b a L hL⟩

end DeletionGraph.ExponentAbsorption
namespace DeletionGraph.WitnessCount
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def Family (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R c : ℕ) : Set (Finset (Spectrum α L)) :=
  {F | GeneratingSet k t b v F ∧ F.card=R ∧ componentCount F=c}

def Allowed (t L R c : ℕ) : Prop :=
  c ≤ (2*t-1)*R+1 ∧ (R ≤ L → c ≤ (2*t-1)*R)

def Candidate (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) (F : Finset (Spectrum α L)) : Prop :=
  GeneratingSet k t b v F ∧ F.card=R ∧ Allowed t L R (componentCount F)

abbrev CIndex (t L R : ℕ) := {c : Fin (2*t*R+1) // Allowed t L R c.val}

noncomputable instance (t L R : ℕ) : Fintype (CIndex t L R) := by
  classical
  unfold CIndex
  infer_instance

theorem index_card (t L R : ℕ) : Fintype.card (CIndex t L R) ≤ 2*t*R+1 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_subtype_le (fun c : Fin (2*t*R+1) => Allowed t L R c.val)

theorem allowed_le {t L R c : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R) (hc : Allowed t L R c) :
    c ≤ 2*t*R := by
  have hs : (2*t-1)*R+R=2*t*R := by
    calc
      _ = (2*t-1+1)*R := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]
  have hh := hc.1
  omega

abbrev Indexed (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) :=
  Σ c : CIndex t L R, Family k t b v R c.val.val

noncomputable def partition (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ)
    (ht : 1 ≤ t) (hR : 1 ≤ R) :
    {F // Candidate k t b v R F} → Indexed k t b v R :=
  fun F => ⟨⟨⟨componentCount F.val,by have h := allowed_le ht hR F.property.2.2;omega⟩,F.property.2.2⟩,
    ⟨F.val,F.property.1,F.property.2.1,rfl⟩⟩

theorem partition_injective (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ)
    (ht : 1 ≤ t) (hR : 1 ≤ R) : Function.Injective (partition k t b v R ht hR) := by
  intro F H heq
  apply Subtype.ext
  exact congrArg (fun z : Indexed k t b v R => z.2.val) heq

theorem component_power (q t L n R c : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hbonus : L < R → n ≤ q^R) (hc : Allowed t L R c) :
    n^c ≤ q^R*n^((2*t-1)*R) := by
  by_cases hs : R ≤ L
  · calc
      _ ≤ n^((2*t-1)*R) := Nat.pow_le_pow_right hn (hc.2 hs)
      _ ≤ q^R*n^((2*t-1)*R) := by
        have hp : 1 ≤ q^R := one_le_pow₀ hq
        simpa only [one_mul] using Nat.mul_le_mul_right (n^((2*t-1)*R)) hp
  · calc
      _ ≤ n^((2*t-1)*R+1) := Nat.pow_le_pow_right hn hc.1
      _ = n*n^((2*t-1)*R) := by rw [pow_succ,Nat.mul_comm]
      _ ≤ q^R*n^((2*t-1)*R) := Nat.mul_le_mul_right _ (hbonus (by omega))

theorem finite_and_card (q n k L t b A R : ℕ) (v : Spectrum α L)
    (ht : 1 ≤ t) (hR : 1 ≤ R) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hbonus : L < R → n ≤ q^R)
    (hcount : ∀ c, c ≤ 2*t*R → generatingCount k t b v R c ≤
      ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    Finite {F // Candidate k t b v R F} ∧
      Nat.card {F // Candidate k t b v R F} ≤
        (2*t*R+1)*q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R) := by
  classical
  have hf (c : CIndex t L R) :
      (Family k t b v R c.val.val).Finite ∧
      (Family k t b v R c.val.val).ncard ≤ n^c.val.val*q^(6*b*t*R)*(L*R)^(A*R) :=
    Set.encard_le_coe_iff_finite_ncard_le.mp (hcount c.val.val (by have h := c.val.isLt;omega))
  letI : ∀ c : CIndex t L R, Finite (Family k t b v R c.val.val) := fun c => (hf c).1.to_subtype
  letI : Finite (Indexed k t b v R) := by unfold Indexed;infer_instance
  have hfin : Finite {F // Candidate k t b v R F} :=
    Finite.of_injective (partition k t b v R ht hR) (partition_injective k t b v R ht hR)
  refine ⟨hfin,?_⟩
  calc
    _ ≤ Nat.card (Indexed k t b v R) :=
      Nat.card_le_card_of_injective (partition k t b v R ht hR) (partition_injective k t b v R ht hR)
    _ = ∑ c : CIndex t L R, Nat.card (Family k t b v R c.val.val) := Nat.card_sigma
    _ ≤ ∑ _c : CIndex t L R, q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R) := by
      apply Finset.sum_le_sum
      intro c hc
      exact (hf c).2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (component_power q t L n R c.val.val hq hn hbonus c.property)))
    _ = Fintype.card (CIndex t L R)*(q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R)) := by simp
    _ ≤ (2*t*R+1)*(q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R)) :=
      Nat.mul_le_mul_right _ (index_card t L R)
    _ = _ := by ring

theorem bonus (q n t b k L R : ℕ) (hreg : Regime q n t b k L) (hR : L < R) :
    n ≤ q^R := by
  have hq : 1 < q := by have h := hreg.1;omega
  have hk := hreg.2.2.2.1
  have hL := hreg.2.2.2.2.1
  have he : uniqueLength q n=2*Nat.clog q n+2 := by
    change 2*⌈Real.logb (q:ℝ) (n:ℝ)⌉₊+2=_
    rw [Real.natCeil_logb_natCast]
  rw [he] at hk
  exact (Nat.le_pow_clog hq n).trans (Nat.pow_le_pow_right (by omega) (by omega))

end DeletionGraph.WitnessCount
namespace DeletionGraph.HashUniform
open DeletionHash.MixedEdit
universe u
theorem joint {α : Type u} [Fintype α] [DecidableEq α] {L r R : ℕ}
    (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) (a : Fin R → Label r) :
    uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      1 / ((2 : ℝ)^r)^R := by
  by_cases hr : 1≤r
  · exact (DeletionHash.MixedEdit.independent_differences L r R 0 0 0 hr w hw).1 a
  · have hr0 : r=0 := by omega
    subst r
    have he : (fun ξ : HashSample α L 0 => ∀ i, hash ξ (w i) = a i) = (fun _ => True) := by
      funext ξ
      apply propext
      exact ⟨fun _ => trivial, fun _ _ => Subsingleton.elim _ _⟩
    rw [he]
    simp [uniformProbability,Nat.card_eq_fintype_card]
end DeletionGraph.HashUniform

namespace DeletionGraph.WitnessProbability
open DeletionHash.MixedEdit WitnessCount ExceptionalProbability
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {n k L t b r R : ℕ}

def Test (F : Finset (Spectrum α L)) (ξ : HashSample α L r) : Prop :=
  ∀ w ∈ F, hash ξ w=0

def Event (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) (ξ : HashSample α L r) : Prop :=
  ∃ F, Candidate k t b v R F ∧ Test F ξ

theorem ruleSet_card (G : Fin R → Spectrum α L)
    (hi : LinearIndependent (ZMod 2) (fun j => parity (G j))) : (ruleSet G).card=R := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  have hinj : Function.Injective G := fun i j h => hi.injective (congrArg parity h)
  unfold ruleSet
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem test_probability (v : Spectrum α L) (F : Finset (Spectrum α L))
    (hg : GeneratingSet k t b v F) :
    uniformProbability (Test (r:=r) F)=1/((2:ℝ)^r)^F.card := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  obtain ⟨G,hgen,hset⟩ := hg
  have he : Test (r:=r) F=(fun ξ => ∀ j, hash ξ (G j)=0) := by
    funext ξ
    apply propext
    constructor
    · intro h j
      apply h
      rw [←hset]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · intro h w hw
      rw [←hset] at hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      exact h j
  rw [he]
  exact HashUniform.joint G hgen.2.1 (fun _ => 0)

theorem event_bound (v : Spectrum α L) (hfinite : Finite {F // Candidate k t b v R F}) :
    uniformProbability (Event (r:=r) k t b v R) ≤
      (Nat.card {F // Candidate k t b v R F} : ℝ)/((2:ℝ)^r)^R := by
  classical
  letI : Finite {F // Candidate k t b v R F} := hfinite
  letI : Fintype {F // Candidate k t b v R F} := Fintype.ofFinite _
  have hcover : ∀ ξ, Event (r:=r) k t b v R ξ →
      ∃ F ∈ (Finset.univ : Finset {F // Candidate k t b v R F}), Test F.val ξ := by
    rintro ξ ⟨F,hF,hT⟩
    exact ⟨⟨F,hF⟩,Finset.mem_univ _,hT⟩
  calc
    _ ≤ uniformProbability (fun ξ => ∃ F ∈ (Finset.univ : Finset {F // Candidate k t b v R F}),
        Test F.val ξ) := probability_mono hcover
    _ ≤ ∑ F : {F // Candidate k t b v R F}, uniformProbability (Test (r:=r) F.val) :=
      probability_union _ _
    _ = ∑ _F : {F // Candidate k t b v R F}, 1/((2:ℝ)^r)^R := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [test_probability v F.val F.property.1,F.property.2.1]
    _ = _ := by simp [Nat.card_eq_fintype_card,div_eq_mul_inv]

theorem bad_cover (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (hr : 1 ≤ r) (x : Word α n) :
    ∀ ξ : HashSample α L r, BadComponent n k t b ξ x →
      ∃ R ∈ Finset.Icc 2 (witnessBound t b L), Event k t b (spectrum L (letters x)) R ξ := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  intro ξ hbad
  obtain ⟨R,G,hgen,hsurv,hR,hmax,hcomp,hsmall⟩ :=
    DeletionHash.MixedEdit.bounded_witness n t b k L r hreg hr ξ x hbad
  have hcard := ruleSet_card G hgen.2.1
  have hset : GeneratingSet k t b (spectrum L (letters x)) (ruleSet G) := by
    unfold GeneratingSet
    rw [hcard]
    exact ⟨G,hgen,rfl⟩
  refine ⟨R,Finset.mem_Icc.mpr ⟨hR,hmax⟩,ruleSet G,⟨hset,hcard,hcomp,hsmall⟩,?_⟩
  intro w hw
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
  exact (hsurv j).2

end DeletionGraph.WitnessProbability
namespace DeletionGraph.OddBound
open DeletionHash.MixedEdit WitnessCount WitnessProbability ExceptionalProbability
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def scale (q n t b L lam : ℕ) : ℕ := q^(6*b*t+1)*n^(2*t-1)*L^lam

theorem candidate_scale (q n k L t b A lam R : ℕ) (v : Spectrum α L)
    (hreg : Regime q n t b k L) (hR : 2 ≤ R) (hmax : R ≤ witnessBound t b L)
    (hexp : ExponentBound t b A lam L)
    (hcount : ∀ c, c ≤ 2*t*R → generatingCount k t b v R c ≤
      ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    Finite {F // Candidate k t b v R F} ∧
      Nat.card {F // Candidate k t b v R F} ≤ (scale q n t b L lam)^R := by
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  obtain ⟨hf,hcard⟩ := finite_and_card q n k L t b A R v (by omega) (by omega)
    (by omega) (by omega) (bonus q n t b k L R ⟨hq,ht,hb,hk,hL,hbk,hLn⟩) hcount
  refine ⟨hf,hcard.trans ?_⟩
  calc
    _ = q^R*n^((2*t-1)*R)*q^(6*b*t*R)*((2*t*R+1)*(L*R)^(A*R)) := by ring
    _ ≤ q^R*n^((2*t-1)*R)*q^(6*b*t*R)*L^(lam*R) :=
      Nat.mul_le_mul_left _ (hexp R hR hmax)
    _ = _ := by
      simp only [scale,mul_pow,←pow_mul]
      rw [show (6*b*t+1)*R=6*b*t*R+R by ring]
      rw [pow_add]
      ring

theorem survival_term (C N Q R : ℕ) (hC : C ≤ N^R) (hQ : 4*N ≤ Q) (hQpos : 0 < Q) :
    (C:ℝ)/(Q:ℝ)^R ≤ (1/4:ℝ)^R := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hNQ : 4*(N:ℝ) ≤ Q := by exact_mod_cast hQ
  have hratio : (N:ℝ)/Q ≤ 1/4 := by
    rw [div_le_iff₀ hQr]
    linarith
  calc
    _ ≤ (N:ℝ)^R/(Q:ℝ)^R := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hC
    _ = ((N:ℝ)/Q)^R := (div_pow _ _ _).symm
    _ ≤ (1/4:ℝ)^R := by gcongr

theorem geometric_tail_identity (N : ℕ) :
    (∑ i ∈ Finset.range N, (1/4:ℝ)^(i+2))=(1-(1/4:ℝ)^N)/12 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [pow_succ]
    ring

theorem geometric_tail_le (M : ℕ) :
    (∑ R ∈ Finset.Icc 2 M, (1/4:ℝ)^R) ≤ 1/12 := by
  have hset : Finset.Icc 2 M=Finset.Ico 2 (M+1) := by ext i;simp
  rw [hset,Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_comm 2]
  rw [geometric_tail_identity]
  have hp : 0 ≤ (1/4:ℝ)^(M+1-2) := by positivity
  linarith

theorem probability_bound (q n k L t b A lam r : ℕ)
    (hqa : Fintype.card α=q) (hreg : Regime q n t b k L) (hr : 1 ≤ r)
    (hexp : ExponentBound t b A lam L)
    (hQ : 4*scale q n t b L lam ≤ 2^r) (x : Word α n)
    (hcount : ∀ R c, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by
  have hreg' : Regime (Fintype.card α) n t b k L := by simpa only [hqa] using hreg
  calc
    _ ≤ uniformProbability (fun ξ : HashSample α L r =>
        ∃ R ∈ Finset.Icc 2 (witnessBound t b L), Event k t b (spectrum L (letters x)) R ξ) :=
      probability_mono (bad_cover n t b k L r hreg' hr x)
    _ ≤ ∑ R ∈ Finset.Icc 2 (witnessBound t b L),
        uniformProbability (Event (r:=r) k t b (spectrum L (letters x)) R) :=
      probability_union _ _
    _ ≤ ∑ R ∈ Finset.Icc 2 (witnessBound t b L), (1/4:ℝ)^R := by
      apply Finset.sum_le_sum
      intro R hR
      obtain ⟨hRlo,hRhi⟩ := Finset.mem_Icc.mp hR
      obtain ⟨hf,hcard⟩ := candidate_scale q n k L t b A lam R (spectrum L (letters x))
        hreg hRlo hRhi hexp (fun c hc => hcount R c (by omega) hc)
      have hp := event_bound (r:=r) (spectrum L (letters x)) hf
      have ht := survival_term _ (scale q n t b L lam) (2^r) R hcard hQ (by positivity)
      exact hp.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht)
    _ ≤ _ := geometric_tail_le _

end DeletionGraph.OddBound
namespace DeletionGraph.OddTheorem
open DeletionHash.MixedEdit

universe u

/-- Proposition 6.1 with the alphabet-uniform choices and eventual-L regime of §6.1.
The counting estimate is a conclusion here, not an assumed oracle for a selected exponent. -/
theorem rare (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ (∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞)) ∧
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      (∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L) ∧
      ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
        ∀ n k L r : ℕ, Regime q n t b k L → L₀ ≤ L → 1 ≤ r →
        4*q^(6*b*t+1)*n^(2*t-1)*L^lam ≤ 2^r →
        ∀ x : Word α n, IsUnique k (letters x) →
        uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by
  obtain ⟨a,ha,hcount⟩ := DeletionHash.MixedEdit.count_generating_sets.{u} t b ht hb
  obtain ⟨lam,L₀,hlam,hL₀,hexp⟩ := DeletionGraph.ExponentAbsorption.eventual t b a
  refine ⟨a,ha,hcount,lam,L₀,hlam,hL₀,hexp,?_⟩
  intro q α instF instD hqa n k L r hreg hready hr hQ x hx
  apply DeletionGraph.OddBound.probability_bound q n k L t b a lam r hqa hreg hr
    (hexp L hready) _ x (hcount q α hqa n k L hreg x hx)
  simpa [DeletionGraph.OddBound.scale,Nat.mul_assoc] using hQ

end DeletionGraph.OddTheorem

open DeletionHash.MixedEdit

universe u

/-- Proposition 6.1 with the alphabet-uniform choices and eventual-L regime of §6.1.
The counting estimate is a conclusion here, not an assumed oracle for a selected exponent. -/
theorem solution (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ (∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞)) ∧
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      (∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L) ∧
      ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
        ∀ n k L r : ℕ, Regime q n t b k L → L₀ ≤ L → 1 ≤ r →
        4*q^(6*b*t+1)*n^(2*t-1)*L^lam ≤ 2^r →
        ∀ x : Word α n, IsUnique k (letters x) →
        uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by exact DeletionGraph.OddTheorem.rare t b ht hb



#print axioms solution

-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.pairwise_rounding_from_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T19:11:09.356298+00:00
-- url     : https://prove2.me/submissions/bb63297c-be2a-4a25-86d3-09382d65efec

import Definitions.Def_DistributedRounding_WeightedColoring
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Pairwise
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
import Mathlib

-- Solutions/Sol_integer_split.lean

open Classical Finset
noncomputable section
namespace PairwiseProof

lemma split_capacity {A : Type} (S : Finset A) (u : A → ℕ) (m : ℕ)
    (hm : m ≤ ∑ a ∈ S, u a) :
    ∃ z : A → ℕ, (∀ a ∈ S, z a ≤ u a) ∧ (∑ a ∈ S, z a) = m := by
  induction S using Finset.induction_on generalizing m with
  | empty =>
    have hm0 : m = 0 := by simpa using hm
    exact ⟨fun _ => 0,by simp,by simp [hm0]⟩
  | @insert a S ha ih =>
    by_cases hma : m ≤ u a
    · refine ⟨fun b => if b = a then m else 0,?_,?_⟩
      · intro b hb
        by_cases he : b = a
        · simpa only [he,ite_true] using hma
        · simp only [he,ite_false,Nat.zero_le]
      · simp only [sum_ite_eq',mem_insert_self,ite_true]
    · have hrest : m-u a ≤ ∑ b ∈ S, u b := by
        rw [sum_insert ha] at hm
        omega
      obtain ⟨z,hz,hsum⟩ := ih (m-u a) hrest
      refine ⟨fun b => if b = a then u a else z b,?_,?_⟩
      · intro b hb
        rcases mem_insert.mp hb with he | hb
        · simp only [he,ite_true,le_refl]
        · by_cases he : b = a
          · simp only [he,ite_true,le_refl]
          · simpa only [he,ite_false] using hz b hb
      · rw [sum_insert ha,if_pos rfl]
        have he : (∑ b ∈ S, if b = a then u a else z b) = ∑ b ∈ S, z b := by
          apply sum_congr rfl
          intro b hb
          exact if_neg (fun (he : b = a) => ha (he ▸ hb))
        rw [he,hsum]
        omega

lemma half_split {A : Type} (S : Finset A) (u : A → ℕ) (K : ℕ)
    (hu : (∑ a ∈ S, u a) = 2*K) :
    ∃ z : A → ℕ, (∀ a ∈ S, z a ≤ u a) ∧
      (∑ a ∈ S, z a) = K ∧ (∑ a ∈ S, (u a-z a)) = K := by
  obtain ⟨z,hz,hsum⟩ := split_capacity S u K (by rw [hu]; omega)
  refine ⟨z,hz,hsum,?_⟩
  rw [sum_tsub_distrib S hz,hu,hsum]
  omega

lemma half_improves {A : Type} (S : Finset A) (u : A → ℕ) (K : ℕ) (hK : 0 < K)
    (hu : (∑ a ∈ S, u a) = 2*K) (score : A → ℝ) :
    ∃ z : A → ℕ, (∀ a ∈ S, z a ≤ u a) ∧ (∑ a ∈ S, z a) = K ∧
      (∑ a ∈ S, ((u a:ℝ)/(2*K))*score a) ≤ ∑ a ∈ S, ((z a:ℝ)/K)*score a := by
  obtain ⟨z,hz,hs,hcomp⟩ := half_split S u K hu
  have hKR : (K:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have he : (∑ a ∈ S, ((z a:ℝ)/K)*score a)+
      (∑ a ∈ S, ((u a-z a:ℕ):ℝ)/K*score a) =
      2*(∑ a ∈ S, ((u a:ℝ)/(2*K))*score a) := by
    rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [Nat.cast_sub (hz a ha)]
    field_simp
    ring
  by_cases hbetter : (∑ a ∈ S, ((u a:ℝ)/(2*K))*score a) ≤ ∑ a ∈ S, ((z a:ℝ)/K)*score a
  · exact ⟨z,hz,hs,hbetter⟩
  · refine ⟨fun a => u a-z a,fun a ha => Nat.sub_le _ _,hcomp,?_⟩
    nlinarith


end PairwiseProof

-- Solutions/Sol_grid_coarsening.lean

open Classical Finset
noncomputable section
namespace PairwiseProof

def chooseHalf (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ)
    (hK : 0 < K) (hu : (∑ a ∈ S, u a) = 2*K) : ℕ → ℕ :=
  (half_improves S u K hK hu score).choose

def halfChoice (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ) (a : ℕ) : ℕ :=
  if h : 0 < K ∧ (∑ b ∈ S, u b) = 2*K then
    if a ∈ S then chooseHalf S u K (fun b => if b ∈ S then score b else 0) h.1 h.2 a else 0
  else 0

lemma halfChoice_outside (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ)
    (a : ℕ) (ha : a ∉ S) : halfChoice S u K score a = 0 := by
  unfold halfChoice
  split_ifs <;> simp only [ha,ite_false]

lemma halfChoice_spec (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ)
    (hK : 0 < K) (hu : (∑ a ∈ S, u a) = 2*K) :
    (∑ a ∈ S, halfChoice S u K score a) = K ∧
    (∀ a, halfChoice S u K score a ≤ u a) ∧
    (∑ a ∈ S, ((u a:ℝ)/(2*K))*score a) ≤
      ∑ a ∈ S, ((halfChoice S u K score a:ℝ)/K)*score a := by
  let masked := fun b => if b ∈ S then score b else 0
  let hex := half_improves S u K hK hu masked
  have he (a : ℕ) (ha : a ∈ S) : halfChoice S u K score a = hex.choose a := by
    unfold halfChoice
    rw [dif_pos ⟨hK,hu⟩,if_pos ha]
    rfl
  constructor
  · rw [sum_congr rfl (fun a ha => he a ha)]
    exact hex.choose_spec.2.1
  constructor
  · intro a
    by_cases ha : a ∈ S
    · rw [he a ha]
      exact hex.choose_spec.1 a ha
    · rw [halfChoice_outside S u K score a ha]
      omega
  · rw [sum_congr rfl (fun a ha => congrArg (fun n : ℕ => (n:ℝ)/K*score a) (he a ha))]
    have hh := hex.choose_spec.2.2
    have heScore (num : ℕ → ℕ) (den : ℝ) :
        (∑ a ∈ S, ((num a:ℝ)/den)*masked a) = ∑ a ∈ S, ((num a:ℝ)/den)*score a := by
      apply sum_congr rfl
      intro a ha
      simp only [masked,if_pos ha]
    exact ((heScore u (2*K)).symm.le.trans hh).trans_eq (heScore hex.choose K)

lemma halfChoice_congr (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score score' : ℕ → ℝ)
    (he : ∀ a ∈ S, score a = score' a) : halfChoice S u K score = halfChoice S u K score' := by
  have hm : (fun b => if b ∈ S then score b else 0) = (fun b => if b ∈ S then score' b else 0) := by
    funext b
    by_cases hb : b ∈ S
    · rw [if_pos hb,if_pos hb,he b hb]
    · rw [if_neg hb,if_neg hb]
  funext a
  unfold halfChoice
  rw [hm]


lemma halfChoice_gain (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ)
    (hK : 0 < K) (hu : (∑ a ∈ S, u a) = 2*K) :
    0 ≤ ∑ a ∈ S, (((halfChoice S u K score a:ℝ)/K)-(u a:ℝ)/(2*K))*score a := by
  have h := (halfChoice_spec S u K score hK hu).2.2
  simp only [sub_mul,sum_sub_distrib]
  linarith

lemma halfChoice_ratio (S : Finset ℕ) (u : ℕ → ℕ) (K : ℕ) (score : ℕ → ℝ)
    (hK : 0 < K) (hu : (∑ a ∈ S, u a) = 2*K) (a : ℕ) :
    ((halfChoice S u K score a:ℝ)/K) ≤ 2*((u a:ℝ)/(2*K)) := by
  have hk : 0 < (K:ℝ) := by exact_mod_cast hK
  have hle : (halfChoice S u K score a:ℝ) ≤ (u a:ℝ) := by exact_mod_cast (halfChoice_spec S u K score hK hu).2.1 a
  have hh := div_le_div_of_nonneg_right hle hk.le
  have he : 2*((u a:ℝ)/(2*K)) = (u a:ℝ)/K := by field_simp
  rwa [he]

end PairwiseProof

-- Solutions/Sol_pairwise_expectation.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Expectation
variable {I : Type} [Fintype I] (labels : I → Finset ℕ) (p : I → ℕ → ℝ)

def expectation (f : (I → ℕ) → ℝ) : ℝ :=
  ∑ s : (i : I) → ↥(labels i), (∏ i, p i (s i)) * f (fun i => s i)

lemma expectation_add (f g : (I → ℕ) → ℝ) :
    expectation labels p (fun s => f s+g s) = expectation labels p f+expectation labels p g := by
  simp only [expectation,mul_add,sum_add_distrib]

lemma expectation_sum {J : Type} (S : Finset J) (f : J → (I → ℕ) → ℝ) :
    expectation labels p (fun s => ∑ j ∈ S, f j s) = ∑ j ∈ S, expectation labels p (f j) := by
  unfold expectation
  simp_rw [mul_sum]
  exact sum_comm

lemma expectation_mul (f : (I → ℕ) → ℝ) (c : ℝ) :
    expectation labels p (fun s => c*f s) = c*expectation labels p f := by
  unfold expectation
  simp_rw [←mul_assoc,mul_comm (∏ i, p i _) c,mul_assoc]
  exact (mul_sum _ _ _).symm

lemma expectation_product (g : I → ℕ → ℝ) :
    expectation labels p (fun s => ∏ i, g i (s i)) =
      ∏ i, ∑ a ∈ labels i, p i a*g i a := by
  unfold expectation
  simp_rw [←prod_mul_distrib]
  apply (Fintype.prod_sum (fun (i : I) (a : ↥(labels i)) => p i a*g i a)).symm.trans
  apply prod_congr rfl
  intro i hi
  exact sum_coe_sort (labels i) (fun a => p i a*g i a)

lemma expectation_unary (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (g : I → ℕ → ℝ) (v : I) :
    expectation labels p (fun s => g v (s v)) = ∑ a ∈ labels v, p v a*g v a := by
  let G := fun i a => if i = v then g i a else 1
  have hp : ∀ s : I → ℕ, (∏ i, G i (s i)) = g v (s v) := by
    intro s
    exact Fintype.prod_ite_eq' v (fun i => g i (s i))
  have hg (i : I) : (∑ a ∈ labels i, p i a*G i a) =
      if i = v then (∑ a ∈ labels i, p i a*g i a) else 1 := by
    by_cases hi : i = v
    · simp only [G,hi,ite_true]
    · simp only [G,hi,ite_false,mul_one,hn]
  have he := expectation_product labels p G
  simp only [hp,hg,Fintype.prod_ite_eq'] at he
  exact he

lemma expectation_two_factors (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (g h : I → ℕ → ℝ) (v w : I) (hvw : v ≠ w) :
    expectation labels p (fun s => g v (s v)*h w (s w)) =
      (∑ a ∈ labels v, p v a*g v a)*(∑ a ∈ labels w, p w a*h w a) := by
  let G := fun i a => (if i = v then g i a else 1)*(if i = w then h i a else 1)
  have hp : ∀ s : I → ℕ, (∏ i, G i (s i)) = g v (s v)*h w (s w) := by
    intro s
    simp only [G,prod_mul_distrib,Fintype.prod_ite_eq']
  have hg (i : I) : (∑ a ∈ labels i, p i a*G i a) =
      (if i = v then (∑ a ∈ labels i, p i a*g i a) else 1)*
      (if i = w then (∑ a ∈ labels i, p i a*h i a) else 1) := by
    by_cases hi : i = v
    · subst i
      simp only [G,ite_true,if_neg hvw,mul_one]
    · by_cases hj : i = w
      · subst i
        simp only [G,if_neg hi,ite_true,one_mul]
      · simp only [G,if_neg hi,if_neg hj,mul_one,hn]
  have he := expectation_product labels p G
  simp only [hp,hg,prod_mul_distrib,Fintype.prod_ite_eq'] at he
  exact he

lemma expectation_congr (f g : (I → ℕ) → ℝ)
    (h : ∀ s : (i : I) → ↥(labels i), f (fun i => s i) = g (fun i => s i)) :
    expectation labels p f = expectation labels p g := by
  unfold expectation
  apply sum_congr rfl
  intro s hs
  rw [h s]

lemma expectation_pair (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (v w : I) (hvw : v ≠ w) (f : ℕ → ℕ → ℝ) :
    expectation labels p (fun s => f (s v) (s w)) =
      ∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*f a b := by
  have hexpand : expectation labels p (fun s => f (s v) (s w)) =
      expectation labels p (fun s => ∑ a ∈ labels v, ∑ b ∈ labels w,
        f a b*((if s v = a then (1:ℝ) else 0)*(if s w = b then (1:ℝ) else 0))) := by
    apply expectation_congr
    intro s
    simp only [mul_ite,mul_one,mul_zero,ite_mul,one_mul,zero_mul]
    rw [sum_eq_single (s v).val]
    · rw [sum_eq_single (s w).val]
      · simp only [ite_true]
      · intro b hb hne
        simp only [Ne.symm hne,ite_false]
      · exact fun h => (h (s w).property).elim
    · intro a ha hne
      simp only [Ne.symm hne,ite_false,ite_self,sum_const_zero]
    · exact fun h => (h (s v).property).elim
  rw [hexpand,expectation_sum]
  apply sum_congr rfl
  intro a ha
  rw [expectation_sum]
  apply sum_congr rfl
  intro b hb
  rw [expectation_mul]
  have he := expectation_two_factors labels p hn
    (fun _ x => if x = a then (1:ℝ) else 0) (fun _ x => if x = b then (1:ℝ) else 0) v w hvw
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq',if_pos ha,if_pos hb] at he
  simp only [mul_ite,mul_one,mul_zero]
  rw [he]
  ring


def mean {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (unary : Fin N → ℕ → ℝ)
    (pair : Fin N → Fin N → ℕ → ℕ → ℝ) : ℝ :=
  (∑ v, ∑ a ∈ labels v, p v a*unary v a)+
    ∑ v, ∑ w ∈ H.neighborFinset v, ∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*pair v w a b

lemma expectation_value {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (hn : ∀ i, ∑ a ∈ labels i, p i a = 1)
    (unary : Fin N → ℕ → ℝ) (pair : Fin N → Fin N → ℕ → ℕ → ℝ) :
    expectation labels p (fun s => (∑ v, unary v (s v))+
      ∑ v, ∑ w ∈ H.neighborFinset v, pair v w (s v) (s w)) = mean H labels p unary pair := by
  rw [expectation_add,expectation_sum,expectation_sum]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl
    intro v hv
    exact expectation_unary labels p hn unary v
  · apply sum_congr rfl
    intro v hv
    rw [expectation_sum]
    apply sum_congr rfl
    intro w hw
    exact expectation_pair labels p hn v w ((SimpleGraph.mem_neighborFinset H v w).mp hw).ne (pair v w)

lemma finiteExpectation_eq {N : ℕ} (D : PairwiseInstance N) (f : (Fin N → ℕ) → ℝ) :
    finiteExpectation D f = expectation D.labels D.probability f := by
  unfold finiteExpectation expectation
  apply sum_congr
  · ext s
    simp only [mem_univ]
  · intro s hs
    rfl

lemma finiteExpectation_utility {N : ℕ} (D : PairwiseInstance N)
    (hn : ∀ v, ∑ a ∈ D.labels v, D.probability v a = 1) :
    finiteExpectation D (utility D) = mean D.graph D.labels D.probability D.unaryUtility D.pairUtility := by
  rw [finiteExpectation_eq]
  exact expectation_value D.graph D.labels D.probability hn D.unaryUtility D.pairUtility

lemma finiteExpectation_cost {N : ℕ} (D : PairwiseInstance N)
    (hn : ∀ v, ∑ a ∈ D.labels v, D.probability v a = 1) :
    finiteExpectation D (cost D) = mean D.graph D.labels D.probability D.unaryCost D.pairCost := by
  rw [finiteExpectation_eq]
  exact expectation_value D.graph D.labels D.probability hn D.unaryCost D.pairCost


end Expectation
end PairwiseProof

-- Solutions/Sol_pairwise_mean.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Mean
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ)
    (B : Fin N → Fin N → ℕ → ℕ → ℝ)

lemma mean_nonneg (hp : ∀ v a, 0 ≤ p v a) (hU : ∀ v a, 0 ≤ U v a)
    (hB : ∀ v w a b, 0 ≤ B v w a b) : 0 ≤ mean H labels p U B := by
  unfold mean
  exact add_nonneg
    (sum_nonneg (fun v _ => sum_nonneg (fun a _ => mul_nonneg (hp v a) (hU v a))))
    (sum_nonneg (fun v _ => sum_nonneg (fun w _ => sum_nonneg (fun a _ =>
      sum_nonneg (fun b _ => mul_nonneg (mul_nonneg (hp v a) (hp w b)) (hB v w a b))))))

lemma mean_sub_smul (C : Fin N → ℕ → ℝ) (D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) :
    mean H labels p (fun v a => U v a-eta*C v a) (fun v w a b => B v w a b-eta*D v w a b) =
      mean H labels p U B-eta*mean H labels p C D := by
  have hu (v : Fin N) (a : ℕ) : p v a*(U v a-eta*C v a) = p v a*U v a-eta*(p v a*C v a) := by ring
  have hb (v w : Fin N) (a b : ℕ) : p v a*p w b*(B v w a b-eta*D v w a b) =
      p v a*p w b*B v w a b-eta*(p v a*p w b*D v w a b) := by ring
  unfold mean
  simp_rw [hu,hb,sum_sub_distrib,←mul_sum]
  ring

lemma mean_interval (q : Fin N → ℕ → ℝ) (lower upper : ℝ)
    (hl : 0 ≤ lower) (hl1 : lower ≤ 1) (hu : 1 ≤ upper)
    (hp : ∀ v a, 0 ≤ p v a) (hq : ∀ v a, 0 ≤ q v a)
    (hlo : ∀ v a, lower*p v a ≤ q v a) (hup : ∀ v a, q v a ≤ upper*p v a)
    (hU : ∀ v a, 0 ≤ U v a) (hB : ∀ v w a b, 0 ≤ B v w a b) :
    lower^2*mean H labels p U B ≤ mean H labels q U B ∧
      mean H labels q U B ≤ upper^2*mean H labels p U B := by
  have hlowU (v : Fin N) (a : ℕ) : lower^2*(p v a*U v a) ≤ q v a*U v a := by
    have hh := mul_le_mul_of_nonneg_right (hlo v a) (hU v a)
    have hpp := mul_nonneg (hp v a) (hU v a)
    have hs : lower^2 ≤ lower := by nlinarith
    nlinarith
  have hhighU (v : Fin N) (a : ℕ) : q v a*U v a ≤ upper^2*(p v a*U v a) := by
    have hh := mul_le_mul_of_nonneg_right (hup v a) (hU v a)
    have hpp := mul_nonneg (hp v a) (hU v a)
    have hs : upper ≤ upper^2 := by nlinarith
    nlinarith
  have hlowB (v w : Fin N) (a b : ℕ) : lower^2*(p v a*p w b*B v w a b) ≤ q v a*q w b*B v w a b := by
    have hh := mul_le_mul (hlo v a) (hlo w b) (mul_nonneg hl (hp w b)) (hq v a)
    have hm := mul_le_mul_of_nonneg_right hh (hB v w a b)
    nlinarith
  have hhighB (v w : Fin N) (a b : ℕ) : q v a*q w b*B v w a b ≤ upper^2*(p v a*p w b*B v w a b) := by
    have hh := mul_le_mul (hup v a) (hup w b) (hq w b) (mul_nonneg (by linarith) (hp v a))
    have hm := mul_le_mul_of_nonneg_right hh (hB v w a b)
    nlinarith
  constructor
  · unfold mean
    rw [mul_add]
    apply add_le_add
    · simp only [mul_sum]
      exact sum_le_sum (fun v _ => sum_le_sum (fun a _ => hlowU v a))
    · simp only [mul_sum]
      exact sum_le_sum (fun v _ => sum_le_sum (fun w _ => sum_le_sum (fun a _ => sum_le_sum (fun b _ => hlowB v w a b))))
  · unfold mean
    rw [mul_add]
    apply add_le_add
    · simp only [mul_sum]
      exact sum_le_sum (fun v _ => sum_le_sum (fun a _ => hhighU v a))
    · simp only [mul_sum]
      exact sum_le_sum (fun v _ => sum_le_sum (fun w _ => sum_le_sum (fun a _ => sum_le_sum (fun b _ => hhighB v w a b))))

end Mean
end PairwiseProof

-- Solutions/Sol_pairwise_local_score.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Scores
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)

def edgeSum (F : Fin N → Fin N → ℕ → ℕ → ℝ) : ℝ :=
  ∑ v, ∑ w ∈ H.neighborFinset v, ∑ a ∈ labels v, ∑ b ∈ labels w, F v w a b

lemma edgeSum_congr (F G : Fin N → Fin N → ℕ → ℕ → ℝ)
    (h : ∀ v w, H.Adj v w → ∀ a ∈ labels v, ∀ b ∈ labels w, F v w a b = G v w a b) :
    edgeSum H labels F = edgeSum H labels G := by
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro w hw
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  exact h v w ((SimpleGraph.mem_neighborFinset H v w).mp hw) a ha b hb

lemma edgeSum_add (F G : Fin N → Fin N → ℕ → ℕ → ℝ) :
    edgeSum H labels (fun v w a b => F v w a b+G v w a b) = edgeSum H labels F+edgeSum H labels G := by
  simp only [edgeSum,sum_add_distrib]

lemma edgeSum_sub (F G : Fin N → Fin N → ℕ → ℕ → ℝ) :
    edgeSum H labels (fun v w a b => F v w a b-G v w a b) = edgeSum H labels F-edgeSum H labels G := by
  simp only [edgeSum,sum_sub_distrib]

lemma neighbor_swap (f : Fin N → Fin N → ℝ) :
    (∑ v, ∑ w ∈ H.neighborFinset v, f v w) = ∑ v, ∑ w ∈ H.neighborFinset v, f w v := by
  have hn (v : Fin N) : H.neighborFinset v = univ.filter (H.Adj v) := by ext u; simp
  simp only [hn,Finset.sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  rw [H.adj_comm]

lemma edgeSum_swap (F : Fin N → Fin N → ℕ → ℕ → ℝ) :
    edgeSum H labels F = edgeSum H labels (fun v w a b => F w v b a) := by
  unfold edgeSum
  rw [neighbor_swap]
  apply sum_congr rfl
  intro v hv
  apply sum_congr rfl
  intro w hw
  exact sum_comm

def localScore (p : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ)
    (B : Fin N → Fin N → ℕ → ℕ → ℝ) (v : Fin N) (a : ℕ) : ℝ :=
  U v a + ∑ w ∈ H.neighborFinset v, ∑ b ∈ labels w, p w b*(B v w a b+B w v b a)

lemma sum_local_terms (delta U : Fin N → ℕ → ℝ) (F : Fin N → Fin N → ℕ → ℕ → ℝ) :
    (∑ v, ∑ a ∈ labels v, delta v a*(U v a+∑ w ∈ H.neighborFinset v, ∑ b ∈ labels w, F v w a b)) =
      (∑ v, ∑ a ∈ labels v, delta v a*U v a)+edgeSum H labels (fun v w a b => delta v a*F v w a b) := by
  simp_rw [mul_add,mul_sum,sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro v hv
  exact sum_comm

lemma sum_local_score (delta p U : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) :
    (∑ v, ∑ a ∈ labels v, delta v a*localScore H labels p U B v a) =
      (∑ v, ∑ a ∈ labels v, delta v a*U v a)+
      edgeSum H labels (fun v w a b => delta v a*p w b*B v w a b)+
      edgeSum H labels (fun v w a b => delta v a*p w b*B w v b a) := by
  unfold localScore
  rw [sum_local_terms]
  have he : edgeSum H labels (fun v w a b => delta v a*(p w b*(B v w a b+B w v b a))) =
      edgeSum H labels (fun v w a b => delta v a*p w b*B v w a b)+
      edgeSum H labels (fun v w a b => delta v a*p w b*B w v b a) := by
    rw [←edgeSum_add]
    apply edgeSum_congr
    intros
    ring
  rw [he]
  ring

end Scores
end PairwiseProof

-- Solutions/Sol_pairwise_parallel.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Parallel
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p q : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ)
    (B : Fin N → Fin N → ℕ → ℕ → ℝ)

lemma parallel_mean_difference (S : Finset (Fin N))
    (hS : ∀ v ∈ S, ∀ w ∈ S, ¬ H.Adj v w)
    (hfix : ∀ v, v ∉ S → ∀ a, q v a = p v a) :
    mean H labels q U B-mean H labels p U B =
      ∑ v, ∑ a ∈ labels v, (q v a-p v a)*localScore H labels p U B v a := by
  have hlinear : edgeSum H labels (fun v w a b => q v a*q w b*B v w a b)-
      edgeSum H labels (fun v w a b => p v a*p w b*B v w a b) =
      edgeSum H labels (fun v w a b => (q v a-p v a)*p w b*B v w a b)+
      edgeSum H labels (fun v w a b => p v a*(q w b-p w b)*B v w a b) := by
    rw [←edgeSum_sub,←edgeSum_add]
    apply edgeSum_congr
    intro v w hvw a ha b hb
    by_cases hv : v ∈ S
    · have hw : w ∉ S := fun hw => hS v hv w hw hvw
      rw [hfix w hw b]
      ring
    · rw [hfix v hv a]
      ring
  have hincoming : edgeSum H labels (fun v w a b => p v a*(q w b-p w b)*B v w a b) =
      edgeSum H labels (fun v w a b => (q v a-p v a)*p w b*B w v b a) := by
    rw [edgeSum_swap]
    apply edgeSum_congr
    intros
    ring
  have hunary : (∑ v, ∑ a ∈ labels v, q v a*U v a)-(∑ v, ∑ a ∈ labels v, p v a*U v a) =
      ∑ v, ∑ a ∈ labels v, (q v a-p v a)*U v a := by
    simp only [sub_mul,sum_sub_distrib]
  rw [sum_local_score,←hincoming]
  change ((∑ v, ∑ a ∈ labels v, q v a*U v a)+edgeSum H labels (fun v w a b => q v a*q w b*B v w a b))-
      ((∑ v, ∑ a ∈ labels v, p v a*U v a)+edgeSum H labels (fun v w a b => p v a*p w b*B v w a b)) = _
  linear_combination hunary+hlinear

lemma parallel_mean_nondecreasing (S : Finset (Fin N))
    (hS : ∀ v ∈ S, ∀ w ∈ S, ¬ H.Adj v w)
    (hfix : ∀ v, v ∉ S → ∀ a, q v a = p v a)
    (himprove : ∀ v ∈ S, 0 ≤ ∑ a ∈ labels v, (q v a-p v a)*localScore H labels p U B v a) :
    mean H labels p U B ≤ mean H labels q U B := by
  have he := parallel_mean_difference H labels p q U B S hS hfix
  have hnonneg : 0 ≤ ∑ v, ∑ a ∈ labels v, (q v a-p v a)*localScore H labels p U B v a := by
    apply sum_nonneg
    intro v hv
    by_cases hs : v ∈ S
    · exact himprove v hs
    · simp only [hfix v hs,sub_self,zero_mul,sum_const_zero,le_refl]
  linarith

end Parallel
end PairwiseProof

-- Solutions/Sol_pairwise_monochromatic.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Mono
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)

def bichromaticGraph (col : Fin N → ℕ) : SimpleGraph (Fin N) where
  Adj v w := H.Adj v w ∧ col v ≠ col w
  symm := ⟨by intro v w h; exact ⟨h.1.symm,Ne.symm h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1.ne rfl⟩

lemma bichromatic_neighbors (col : Fin N → ℕ) (v : Fin N) :
    (bichromaticGraph H col).neighborFinset v = (H.neighborFinset v).filter (fun w => col v ≠ col w) := by
  ext w
  rw [SimpleGraph.mem_neighborFinset,mem_filter,SimpleGraph.mem_neighborFinset]
  rfl

lemma color_class_independent (col : Fin N → ℕ) (c : ℕ) :
    ∀ v ∈ univ.filter (fun v => col v = c), ∀ w ∈ univ.filter (fun w => col w = c),
      ¬ (bichromaticGraph H col).Adj v w := by
  intro v hv w hw hadj
  exact hadj.2 ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)

def edgeMean (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) (v w : Fin N) : ℝ :=
  ∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*B v w a b

def monoPair (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) (col : Fin N → ℕ) : ℝ :=
  ∑ v, ∑ w ∈ H.neighborFinset v, if col v = col w then edgeMean labels p B v w else 0

lemma mean_bichromatic_split (p : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ)
    (B : Fin N → Fin N → ℕ → ℕ → ℝ) (col : Fin N → ℕ) :
    mean H labels p U B = mean (bichromaticGraph H col) labels p U B+monoPair H labels p B col := by
  have he : edgeSum H labels (fun v w a b => p v a*p w b*B v w a b) =
      edgeSum (bichromaticGraph H col) labels (fun v w a b => p v a*p w b*B v w a b)+
      monoPair H labels p B col := by
    unfold edgeSum monoPair edgeMean
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    rw [bichromatic_neighbors,Finset.sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    by_cases hc : col v = col w <;> simp [hc]
  change _+edgeSum H labels (fun v w a b => p v a*p w b*B v w a b) =
    (_+edgeSum (bichromaticGraph H col) labels (fun v w a b => p v a*p w b*B v w a b))+_
  rw [he]
  ring

lemma monoPair_as_mean (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (col : Fin N → ℕ) : monoPair H labels p B col =
      mean H labels p (fun _ _ => 0) (fun v w a b => if col v = col w then B v w a b else 0) := by
  simp only [monoPair,mean,mul_zero,sum_const_zero,zero_add,mul_ite,sum_ite_irrel,edgeMean]

lemma monoPair_nonneg (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (col : Fin N → ℕ) (hp : ∀ v a, 0 ≤ p v a) (hB : ∀ v w a b, 0 ≤ B v w a b) :
    0 ≤ monoPair H labels p B col := by
  rw [monoPair_as_mean]
  apply mean_nonneg H labels p _ _ hp (by intros; rfl)
  intro v w a b
  split_ifs <;> first | exact hB v w a b | rfl

lemma monoPair_quadruple (p q : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (col : Fin N → ℕ) (hp : ∀ v a, 0 ≤ p v a) (hq : ∀ v a, 0 ≤ q v a)
    (hbound : ∀ v a, q v a ≤ 2*p v a) (hB : ∀ v w a b, 0 ≤ B v w a b) :
    monoPair H labels q B col ≤ 4*monoPair H labels p B col := by
  have hb := mean_interval H labels p (fun _ _ => 0)
    (fun v w a b => if col v = col w then B v w a b else 0) q 0 2
    (by norm_num) (by norm_num) (by norm_num) hp hq
    (fun v a => by simpa only [zero_mul] using hq v a) hbound (by intros; rfl)
    (by intro v w a b; split_ifs <;> first | exact hB v w a b | rfl)
  simpa only [←monoPair_as_mean,show (2:ℝ)^2=4 by norm_num] using hb.2

end Mono
end PairwiseProof

-- Solutions/Sol_rounding_colors.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

abbrev NumState (N : ℕ) := Fin N → (ℕ → ℕ) × ℕ

def density {N : ℕ} (st : NumState N) (v : Fin N) (a : ℕ) : ℝ := (st v).1 a/(st v).2

lemma density_nonneg {N : ℕ} (st : NumState N) (v : Fin N) (a : ℕ) : 0 ≤ density st v a := by
  unfold density
  positivity

section ColorRounds
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (U : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) (col : Fin N → ℕ) (K : ℕ)

def roundOne (c : ℕ) (st : NumState N) : NumState N := fun v =>
  if col v = c then
    (halfChoice (labels v) (st v).1 K (localScore (bichromaticGraph H col) labels (density st) U B v),K)
  else st v

def roundColors (u : Fin N → ℕ → ℕ) : ℕ → NumState N
  | 0 => fun v => (u v,2*K)
  | c+1 => roundOne H labels U B col K c (roundColors u c)

lemma roundOne_nondecreasing (hK : 0 < K) (c : ℕ) (st : NumState N)
    (hgrid : ∀ v, col v = c → (st v).2 = 2*K ∧ (∑ a ∈ labels v, (st v).1 a) = 2*K) :
    mean (bichromaticGraph H col) labels (density st) U B ≤
      mean (bichromaticGraph H col) labels (density (roundOne H labels U B col K c st)) U B := by
  let S := univ.filter (fun v => col v = c)
  apply parallel_mean_nondecreasing (bichromaticGraph H col) labels (density st)
    (density (roundOne H labels U B col K c st)) U B S (color_class_independent H col c)
  · intro v hv a
    have hne : col v ≠ c := fun h => hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    unfold density roundOne
    rw [if_neg hne]
  · intro v hv
    have heq := (mem_filter.mp hv).2
    let score := localScore (bichromaticGraph H col) labels (density st) U B v
    have hg := halfChoice_gain (labels v) (st v).1 K score hK (hgrid v heq).2
    have he (a : ℕ) : density (roundOne H labels U B col K c st) v a-density st v a =
        ((halfChoice (labels v) (st v).1 K score a:ℝ)/K)-(st v).1 a/(2*K) := by
      unfold density roundOne
      rw [if_pos heq,(hgrid v heq).1]
      simp only [Nat.cast_mul,Nat.cast_ofNat,score]
    convert hg using 1
    apply sum_congr rfl
    intro a ha
    rw [he]

lemma roundColors_grid (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K) (c : ℕ) : ∀ v,
    (col v < c → (roundColors H labels U B col K u c v).2 = K ∧
      (∑ a ∈ labels v, (roundColors H labels U B col K u c v).1 a) = K ∧
      ∀ a, (roundColors H labels U B col K u c v).1 a ≤ u v a) ∧
    (c ≤ col v → roundColors H labels U B col K u c v = (u v,2*K)) := by
  induction c with
  | zero => intro v; refine ⟨by omega,fun _ => rfl⟩
  | succ c ih =>
    intro v
    by_cases heq : col v = c
    · have hprev := (ih v).2 (by omega)
      have hsp := halfChoice_spec (labels v) (u v) K
        (localScore (bichromaticGraph H col) labels (density (roundColors H labels U B col K u c)) U B v) hK (hu v)
      constructor
      · intro hv
        simp only [roundColors,roundOne,if_pos heq,hprev]
        exact ⟨trivial,hsp.1,hsp.2.1⟩
      · intro hv
        omega
    · have hstate : roundColors H labels U B col K u (c+1) v = roundColors H labels U B col K u c v := by
        simp only [roundColors,roundOne,if_neg heq]
      rw [hstate]
      constructor
      · intro hv
        exact (ih v).1 (by omega)
      · intro hv
        exact (ih v).2 (by omega)

lemma roundColors_nondecreasing (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K) (c : ℕ) :
    mean (bichromaticGraph H col) labels (density (fun v => (u v,2*K))) U B ≤
      mean (bichromaticGraph H col) labels (density (roundColors H labels U B col K u c)) U B := by
  induction c with
  | zero => exact le_rfl
  | succ c ih =>
    apply ih.trans
    apply roundOne_nondecreasing H labels U B col K hK c
    intro v hv
    have he := (roundColors_grid H labels U B col K hK u hu c v).2 (by omega)
    rw [he]
    exact ⟨rfl,hu v⟩

lemma roundColors_ratio (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K) (c : ℕ) (v : Fin N) (a : ℕ) :
    density (roundColors H labels U B col K u c) v a ≤ 2*((u v a:ℝ)/(2*K)) := by
  have hs := roundColors_grid H labels U B col K hK u hu c v
  have hKR : 0 < (K:ℝ) := by exact_mod_cast hK
  have hid : 2*((u v a:ℝ)/(2*K)) = (u v a:ℝ)/K := by field_simp
  by_cases hv : col v < c
  · have hd := (hs.1 hv).1
    have hn := (hs.1 hv).2.2 a
    unfold density
    rw [hd,hid]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hn) hKR.le
  · have he := hs.2 (by omega)
    unfold density
    rw [he]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hp : 0 ≤ (u v a:ℝ)/(2*K) := by positivity
    linarith

lemma roundColors_final (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K) (M : ℕ) (hcol : ∀ v, col v < M) : ∀ v,
    (roundColors H labels U B col K u M v).2 = K ∧
    (∑ a ∈ labels v, (roundColors H labels U B col K u M v).1 a) = K ∧
    ∀ a, (roundColors H labels U B col K u M v).1 a ≤ u v a := by
  intro v
  exact (roundColors_grid H labels U B col K hK u hu M v).1 (hcol v)

lemma roundColors_outside (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K) (c : ℕ) (v : Fin N) (a : ℕ)
    (hzero : u v a = 0) : (roundColors H labels U B col K u c v).1 a = 0 := by
  have hs := roundColors_grid H labels U B col K hK u hu c v
  by_cases hv : col v < c
  · have hh := (hs.1 hv).2.2 a
    omega
  · rw [hs.2 (by omega)]
    exact hzero


end ColorRounds
end PairwiseProof

-- Solutions/Sol_pairwise_cut_loss.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Loss
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)

lemma edgeMean_add_smul (p : Fin N → ℕ → ℝ)
    (B D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) (v w : Fin N) :
    edgeMean labels p (fun v w a b => B v w a b+eta*D v w a b) v w =
      edgeMean labels p B v w+eta*edgeMean labels p D v w := by
  have he (a b : ℕ) : p v a*p w b*(B v w a b+eta*D v w a b) =
      p v a*p w b*B v w a b+eta*(p v a*p w b*D v w a b) := by ring
  unfold edgeMean
  simp_rw [he,sum_add_distrib,←mul_sum]

lemma monoPair_add_smul (p : Fin N → ℕ → ℝ)
    (B D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) (col : Fin N → ℕ) :
    monoPair H labels p (fun v w a b => B v w a b+eta*D v w a b) col =
      monoPair H labels p B col+eta*monoPair H labels p D col := by
  have he (v w : Fin N) :
      (if col v = col w then edgeMean labels p B v w+eta*edgeMean labels p D v w else 0) =
      (if col v = col w then edgeMean labels p B v w else 0)+
      eta*(if col v = col w then edgeMean labels p D v w else 0) := by
    by_cases h : col v = col w <;> simp only [h,ite_true,ite_false,mul_zero,add_zero]
  unfold monoPair
  simp_rw [edgeMean_add_smul,he,sum_add_distrib,←mul_sum]

lemma mean_add_smul (p : Fin N → ℕ → ℝ) (U C : Fin N → ℕ → ℝ)
    (B D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) :
    mean H labels p (fun v a => U v a+eta*C v a) (fun v w a b => B v w a b+eta*D v w a b) =
      mean H labels p U B+eta*mean H labels p C D := by
  have hu (v : Fin N) (a : ℕ) : p v a*(U v a+eta*C v a) =
      p v a*U v a+eta*(p v a*C v a) := by ring
  have hb (v w : Fin N) (a b : ℕ) : p v a*p w b*(B v w a b+eta*D v w a b) =
      p v a*p w b*B v w a b+eta*(p v a*p w b*D v w a b) := by ring
  unfold mean
  simp_rw [hu,hb,sum_add_distrib,←mul_sum]
  ring

lemma bichromatic_improvement_loss (p q : Fin N → ℕ → ℝ) (U C : Fin N → ℕ → ℝ)
    (B D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) (heta : 0 ≤ eta) (col : Fin N → ℕ)
    (hp : ∀ v a, 0 ≤ p v a) (hq : ∀ v a, 0 ≤ q v a) (hbound : ∀ v a, q v a ≤ 2*p v a)
    (hB : ∀ v w a b, 0 ≤ B v w a b) (hD : ∀ v w a b, 0 ≤ D v w a b)
    (hlocal : mean (bichromaticGraph H col) labels p U B-eta*mean (bichromaticGraph H col) labels p C D ≤
      mean (bichromaticGraph H col) labels q U B-eta*mean (bichromaticGraph H col) labels q C D) :
    mean H labels p U B-eta*mean H labels p C D-
      3*(monoPair H labels p B col+eta*monoPair H labels p D col) ≤
    mean H labels q U B-eta*mean H labels q C D := by
  have hmonoU := monoPair_nonneg H labels p B col hp hB
  have hmonoU' := monoPair_nonneg H labels q B col hq hB
  have hmonoC := monoPair_quadruple H labels p q D col hp hq hbound hD
  have hscaled := mul_le_mul_of_nonneg_left hmonoC heta
  rw [mean_bichromatic_split H labels p U B col,mean_bichromatic_split H labels p C D col,
    mean_bichromatic_split H labels q U B col,mean_bichromatic_split H labels q C D col]
  nlinarith

def pairWeights (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) (v w : Fin N) : ℝ :=
  if H.Adj v w then edgeMean labels p B v w+edgeMean labels p B w v else 0

lemma pairWeights_nonneg (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (hp : ∀ v a, 0 ≤ p v a) (hB : ∀ v w a b, 0 ≤ B v w a b) (v w : Fin N) :
    0 ≤ pairWeights H labels p B v w := by
  have he (v w : Fin N) : 0 ≤ edgeMean labels p B v w :=
    sum_nonneg (fun a _ => sum_nonneg (fun b _ => mul_nonneg (mul_nonneg (hp v a) (hp w b)) (hB v w a b)))
  unfold pairWeights
  split_ifs <;> first | exact add_nonneg (he v w) (he w v) | rfl

lemma pairWeights_symm (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) (v w : Fin N) :
    pairWeights H labels p B v w = pairWeights H labels p B w v := by
  unfold pairWeights
  rw [H.adj_comm v w]
  split_ifs <;> ring

lemma pairWeights_total (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ) :
    (∑ v, ∑ w ∈ H.neighborFinset v, pairWeights H labels p B v w) =
      2*mean H labels p (fun _ _ => 0) B := by
  have he (v w : Fin N) (hw : w ∈ H.neighborFinset v) : pairWeights H labels p B v w =
      edgeMean labels p B v w+edgeMean labels p B w v := if_pos ((SimpleGraph.mem_neighborFinset H v w).mp hw)
  have hs : (∑ v, ∑ w ∈ H.neighborFinset v, pairWeights H labels p B v w) =
      (∑ v, ∑ w ∈ H.neighborFinset v, edgeMean labels p B v w)+
      (∑ v, ∑ w ∈ H.neighborFinset v, edgeMean labels p B w v) := by
    simp_rw [sum_congr rfl (fun w hw => he _ w hw),sum_add_distrib]
  rw [hs,←neighbor_swap H (edgeMean labels p B)]
  simp only [mean,mul_zero,sum_const_zero,zero_add,edgeMean]
  ring

lemma pairWeights_monochromatic (p : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (col : Fin N → ℕ) :
    (∑ v, ∑ w ∈ H.neighborFinset v, if col w = col v then pairWeights H labels p B v w else 0) =
      2*monoPair H labels p B col := by
  let F := fun v w => if col v = col w then edgeMean labels p B v w else 0
  have he (v w : Fin N) (hw : w ∈ H.neighborFinset v) :
      (if col w = col v then pairWeights H labels p B v w else 0) = F v w+F w v := by
    rw [show pairWeights H labels p B v w = edgeMean labels p B v w+edgeMean labels p B w v from
      if_pos ((SimpleGraph.mem_neighborFinset H v w).mp hw)]
    by_cases h : col v = col w
    · simp only [F,if_pos h,if_pos h.symm]
    · simp only [F,if_neg h,if_neg (Ne.symm h),add_zero]
  have hs : (∑ v, ∑ w ∈ H.neighborFinset v, if col w = col v then pairWeights H labels p B v w else 0) =
      (∑ v, ∑ w ∈ H.neighborFinset v, F v w)+(∑ v, ∑ w ∈ H.neighborFinset v, F w v) := by
    simp_rw [sum_congr rfl (fun w hw => he _ w hw),sum_add_distrib]
  rw [hs,←neighbor_swap H F]
  change _ = 2*(∑ v, ∑ w ∈ H.neighborFinset v, F v w)
  ring

lemma mean_zero_unary_le (p : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ)
    (B : Fin N → Fin N → ℕ → ℕ → ℝ) (hp : ∀ v a, 0 ≤ p v a) (hU : ∀ v a, 0 ≤ U v a) :
    mean H labels p (fun _ _ => 0) B ≤ mean H labels p U B := by
  have hu : 0 ≤ ∑ v, ∑ a ∈ labels v, p v a*U v a :=
    sum_nonneg (fun v _ => sum_nonneg (fun a _ => mul_nonneg (hp v a) (hU v a)))
  unfold mean
  simp only [mul_zero,sum_const_zero,zero_add]
  linarith

lemma weighted_one_stage_loss (p q : Fin N → ℕ → ℝ) (U C : Fin N → ℕ → ℝ)
    (B D : Fin N → Fin N → ℕ → ℕ → ℝ) (eta : ℝ) (heta : 0 ≤ eta)
    (col : Fin N → ℕ) (Q : ℕ)
    (hp : ∀ v a, 0 ≤ p v a) (hq : ∀ v a, 0 ≤ q v a) (hbound : ∀ v a, q v a ≤ 2*p v a)
    (hU : ∀ v a, 0 ≤ U v a) (hC : ∀ v a, 0 ≤ C v a)
    (hB : ∀ v w a b, 0 ≤ B v w a b) (hD : ∀ v w a b, 0 ≤ D v w a b)
    (hlocal : mean (bichromaticGraph H col) labels p U B-eta*mean (bichromaticGraph H col) labels p C D ≤
      mean (bichromaticGraph H col) labels q U B-eta*mean (bichromaticGraph H col) labels q C D)
    (hweighted : (Q:ℝ)*(∑ v, ∑ w ∈ H.neighborFinset v, if col w = col v then
        pairWeights H labels p (fun v w a b => B v w a b+eta*D v w a b) v w else 0) ≤
      4*(∑ v, ∑ w ∈ H.neighborFinset v,
        pairWeights H labels p (fun v w a b => B v w a b+eta*D v w a b) v w)) :
    -(12:ℝ)*(mean H labels p U B+eta*mean H labels p C D) ≤
      (Q:ℝ)*((mean H labels q U B-eta*mean H labels q C D)-
        (mean H labels p U B-eta*mean H labels p C D)) := by
  have hmono := bichromatic_improvement_loss H labels p q U C B D eta heta col hp hq hbound hB hD hlocal
  have hfull : mean H labels p (fun _ _ => 0) (fun v w a b => B v w a b+eta*D v w a b) ≤
      mean H labels p U B+eta*mean H labels p C D := by
    rw [←mean_add_smul]
    apply mean_zero_unary_le H labels p _ _ hp
    intro v a
    exact add_nonneg (hU v a) (mul_nonneg heta (hC v a))
  rw [pairWeights_monochromatic,pairWeights_total,monoPair_add_smul] at hweighted
  have hh := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg Q)
  nlinarith


end Loss
end PairwiseProof

-- Solutions/Sol_rounding_stage_math.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Stage
variable {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (U C : Fin N → ℕ → ℝ) (B D : Fin N → Fin N → ℕ → ℕ → ℝ)

def stageState (eta : ℝ) (col : Fin N → ℕ) (K : ℕ) (u : Fin N → ℕ → ℕ) (M : ℕ) : NumState N :=
  roundColors H labels (fun v a => U v a-eta*C v a) (fun v w a b => B v w a b-eta*D v w a b) col K u M

lemma stageState_grid (eta : ℝ) (col : Fin N → ℕ) (K : ℕ) (u : Fin N → ℕ → ℕ)
    (M : ℕ) (hK : 0 < K) (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K)
    (hcol : ∀ v, col v < M) : ∀ v,
    (stageState H labels U C B D eta col K u M v).2 = K ∧
    (∑ a ∈ labels v, (stageState H labels U C B D eta col K u M v).1 a) = K ∧
    ∀ a, (stageState H labels U C B D eta col K u M v).1 a ≤ u v a :=
  roundColors_final H labels _ _ col K hK u hu M hcol

lemma stageState_loss (eta : ℝ) (heta : 0 ≤ eta) (col : Fin N → ℕ) (K : ℕ)
    (u : Fin N → ℕ → ℕ) (M Q : ℕ) (hK : 0 < K)
    (hu : ∀ v, (∑ a ∈ labels v, u v a) = 2*K)
    (hU : ∀ v a, 0 ≤ U v a) (hC : ∀ v a, 0 ≤ C v a)
    (hB : ∀ v w a b, 0 ≤ B v w a b) (hD : ∀ v w a b, 0 ≤ D v w a b)
    (hweighted : let p := density (fun v => (u v,2*K));
      (Q:ℝ)*(∑ v, ∑ w ∈ H.neighborFinset v, if col w = col v then
        pairWeights H labels p (fun v w a b => B v w a b+eta*D v w a b) v w else 0) ≤
      4*(∑ v, ∑ w ∈ H.neighborFinset v,
        pairWeights H labels p (fun v w a b => B v w a b+eta*D v w a b) v w)) :
    let p := density (fun v => (u v,2*K));
    let q := density (stageState H labels U C B D eta col K u M);
    -(12:ℝ)*(mean H labels p U B+eta*mean H labels p C D) ≤
      (Q:ℝ)*((mean H labels q U B-eta*mean H labels q C D)-
        (mean H labels p U B-eta*mean H labels p C D)) := by
  let p := density (fun v => (u v,2*K));
  let q := density (stageState H labels U C B D eta col K u M);
  have hbound (v : Fin N) (a : ℕ) : q v a ≤ 2*p v a := by
    have hh := roundColors_ratio H labels (fun v a => U v a-eta*C v a)
      (fun v w a b => B v w a b-eta*D v w a b) col K hK u hu M v a
    simpa only [p,q,stageState,density,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hlocal := roundColors_nondecreasing H labels (fun v a => U v a-eta*C v a)
    (fun v w a b => B v w a b-eta*D v w a b) col K hK u hu M
  rw [mean_sub_smul,mean_sub_smul] at hlocal
  exact weighted_one_stage_loss H labels p q U C B D eta heta col Q
    (density_nonneg _) (density_nonneg _) hbound hU hC hB hD hlocal hweighted

end Stage
end PairwiseProof

-- Solutions/Sol_objective_messages.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

structure MarginalRecord where
  id : ℕ
  labels : Finset ℕ
  numerator : ℕ → ℕ
  denominator : ℕ
  color : ℕ

def recordProbability (m : MarginalRecord) (a : ℕ) : ℝ := (m.numerator a:ℝ)/m.denominator

def marginalRecord {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (st : NumState N) (col : Fin N → ℕ) (v : Fin N) : MarginalRecord :=
  ⟨ids v,D.labels v,(st v).1,(st v).2,col v⟩

def marginalMessages {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (st : NumState N) (col : Fin N → ℕ) (v : Fin N) : Multiset MarginalRecord :=
  (D.graph.neighborFinset v).val.map (marginalRecord D ids st col)

def pairScore (inp : ObjectiveInput) (eta : ℝ) (id a b : ℕ) : ℝ :=
  ((inp.tables id).1 a b+(inp.tables id).2.2.1 a b)-
    eta*((inp.tables id).2.1 a b+(inp.tables id).2.2.2 a b)

def pairWeight (inp : ObjectiveInput) (eta : ℝ) (id a b : ℕ) : ℝ :=
  ((inp.tables id).1 a b+(inp.tables id).2.2.1 a b)+
    eta*((inp.tables id).2.1 a b+(inp.tables id).2.2.2 a b)

def scoreFromMessages (inp : ObjectiveInput) (eta : ℝ) (color : ℕ)
    (msgs : Multiset MarginalRecord) (a : ℕ) : ℝ :=
  inp.unaryUtility a-eta*inp.unaryCost a+
    (msgs.map fun m => if m.color ≠ color then
      ∑ b ∈ m.labels, recordProbability m b*pairScore inp eta m.id a b else 0).sum

def weightsFromMessages (inp : ObjectiveInput) (eta : ℝ) (num : ℕ → ℕ) (den : ℕ)
    (msgs : Multiset MarginalRecord) (id : ℕ) : ℝ :=
  (msgs.map fun m => if m.id = id then ∑ a ∈ inp.labels, ∑ b ∈ m.labels,
    ((num a:ℝ)/den)*recordProbability m b*pairWeight inp eta m.id a b else 0).sum

lemma neighbor_lookup {N : ℕ} (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (v u : Fin N) (hu : H.Adj v u)
    (P : Fin N → Prop) [DecidablePred P] (f : Fin N → ℝ) (hp : P u) :
    (∑ w ∈ H.neighborFinset v, if ids w = ids u ∧ P w then f w else 0) = f u := by
  rw [sum_eq_single u]
  · simp only [hp,and_self,ite_true]
  · intro w hw hwu
    have hn : ids w ≠ ids u := fun he => hwu (hi he)
    simp only [hn,false_and,ite_false]
  · intro h
    exact (h ((SimpleGraph.mem_neighborFinset H v u).mpr hu)).elim

lemma objective_tables {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (orig : Fin N → ℕ) (v u : Fin N) (hu : D.graph.Adj v u)
    (a b : ℕ) (ha : a ∈ D.labels v) (hb : b ∈ D.labels u) :
    ((objectiveInput D ids orig v).tables (ids u)).1 a b = D.pairUtility v u a b ∧
    ((objectiveInput D ids orig v).tables (ids u)).2.1 a b = D.pairCost v u a b ∧
    ((objectiveInput D ids orig v).tables (ids u)).2.2.1 a b = D.pairUtility u v b a ∧
    ((objectiveInput D ids orig v).tables (ids u)).2.2.2 a b = D.pairCost u v b a := by
  simp only [objectiveInput]
  have h := neighbor_lookup D.graph ids hi v u hu (fun w => a ∈ D.labels v ∧ b ∈ D.labels w)
  exact ⟨h (fun w => D.pairUtility v w a b) ⟨ha,hb⟩,h (fun w => D.pairCost v w a b) ⟨ha,hb⟩,
    h (fun w => D.pairUtility w v b a) ⟨ha,hb⟩,h (fun w => D.pairCost w v b a) ⟨ha,hb⟩⟩

lemma pairScore_correct {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (orig : Fin N → ℕ) (eta : ℝ) (v u : Fin N) (hu : D.graph.Adj v u)
    (a b : ℕ) (ha : a ∈ D.labels v) (hb : b ∈ D.labels u) :
    pairScore (objectiveInput D ids orig v) eta (ids u) a b =
      (D.pairUtility v u a b-eta*D.pairCost v u a b)+
        (D.pairUtility u v b a-eta*D.pairCost u v b a) := by
  have ht := objective_tables D ids hi orig v u hu a b ha hb
  unfold pairScore
  rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
  ring

lemma pairWeight_correct {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (orig : Fin N → ℕ) (eta : ℝ) (v u : Fin N) (hu : D.graph.Adj v u)
    (a b : ℕ) (ha : a ∈ D.labels v) (hb : b ∈ D.labels u) :
    pairWeight (objectiveInput D ids orig v) eta (ids u) a b =
      D.pairUtility v u a b+D.pairUtility u v b a+
        eta*(D.pairCost v u a b+D.pairCost u v b a) := by
  have ht := objective_tables D ids hi orig v u hu a b ha hb
  unfold pairWeight
  rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

lemma scoreFromMessages_correct {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (orig col : Fin N → ℕ) (eta : ℝ) (st : NumState N)
    (v : Fin N) (a : ℕ) (ha : a ∈ D.labels v) :
    scoreFromMessages (objectiveInput D ids orig v) eta (col v)
      (marginalMessages D ids st col v) a =
    localScore (bichromaticGraph D.graph col) D.labels (density st)
      (fun v a => D.unaryUtility v a-eta*D.unaryCost v a)
      (fun v u a b => D.pairUtility v u a b-eta*D.pairCost v u a b) v a := by
  unfold scoreFromMessages marginalMessages
  simp only [Multiset.map_map,Function.comp_def,Finset.sum_val,
    marginalRecord,recordProbability]
  simp only [objectiveInput,if_pos ha]
  unfold localScore
  rw [bichromatic_neighbors]
  rw [Finset.sum_filter]
  congr 1
  apply sum_congr rfl
  intro u hu
  have hAdj := (SimpleGraph.mem_neighborFinset D.graph v u).mp hu
  by_cases hc : col u = col v
  · simp only [hc,ne_eq,not_true_eq_false,ite_false]
  · simp only [ne_eq,hc,Ne.symm hc,not_false_eq_true,ite_true,ite_false]
    apply sum_congr rfl
    intro b hb
    change density st u b * pairScore (objectiveInput D ids orig v) eta (ids u) a b = _
    rw [pairScore_correct D ids hi orig eta v u hAdj a b ha hb]

lemma weightsFromMessages_correct {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (orig col : Fin N → ℕ) (eta : ℝ) (st : NumState N)
    (v u : Fin N) :
    weightsFromMessages (objectiveInput D ids orig v) eta (st v).1 (st v).2
      (marginalMessages D ids st col v) (ids u) =
    pairWeights D.graph D.labels (density st)
      (fun v u a b => D.pairUtility v u a b+eta*D.pairCost v u a b) v u := by
  unfold weightsFromMessages marginalMessages
  simp only [Multiset.map_map,Function.comp_def,Finset.sum_val,marginalRecord,recordProbability]
  change (∑ w ∈ D.graph.neighborFinset v, if ids w = ids u then
    ∑ a ∈ D.labels v, ∑ b ∈ D.labels w, density st v a*density st w b*
      pairWeight (objectiveInput D ids orig v) eta (ids w) a b else 0) = _
  by_cases hAdj : D.graph.Adj v u
  · rw [sum_eq_single u]
    · rw [if_pos rfl,pairWeights,if_pos hAdj]
      have he : (∑ a ∈ D.labels v, ∑ b ∈ D.labels u, density st v a*density st u b*
          pairWeight (objectiveInput D ids orig v) eta (ids u) a b) =
          ∑ a ∈ D.labels v, ∑ b ∈ D.labels u,
            (density st v a*density st u b*(D.pairUtility v u a b+eta*D.pairCost v u a b)+
             density st v a*density st u b*(D.pairUtility u v b a+eta*D.pairCost u v b a)) := by
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        rw [pairWeight_correct D ids hi orig eta v u hAdj a b ha hb]
        ring
      rw [he]
      simp only [sum_add_distrib,edgeMean]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro a ha
      ring
    · intro w hw hwu
      rw [if_neg (fun he => hwu (hi he))]
    · intro hu
      exact (hu ((SimpleGraph.mem_neighborFinset D.graph v u).mpr hAdj)).elim
  · rw [pairWeights,if_neg hAdj]
    apply sum_eq_zero
    intro w hw
    apply if_neg
    intro he
    exact hAdj ((hi he) ▸ (SimpleGraph.mem_neighborFinset D.graph v w).mp hw)

end PairwiseProof

-- Solutions/Sol_probability_quantization.lean

open Classical Finset
noncomputable section
namespace PairwiseProof

lemma rounded_sum {A : Type} (S : Finset A) (x : A → ℝ) (P : ℕ)
    (hx : ∀ a ∈ S, 0 ≤ x a) (hsum : (∑ a ∈ S, x a) = P) :
    ∃ m : A → ℕ, (∑ a ∈ S, m a) = P ∧
      (∀ a ∈ S, |(m a:ℝ)-x a| ≤ 1) ∧ (∀ a ∈ S, x a = 0 → m a = 0) := by
  let floor := fun a => ⌊x a⌋₊
  let capacity := fun a => if (floor a:ℝ) < x a then (1:ℕ) else 0
  have hfloor : (∑ a ∈ S, floor a) ≤ P := by
    have hh : ((∑ a ∈ S, floor a:ℕ):ℝ) ≤ (P:ℝ) := by
      rw [Nat.cast_sum,←hsum]
      exact sum_le_sum (fun a ha => Nat.floor_le (hx a ha))
    exact_mod_cast hh
  have hupper (a : A) (ha : a ∈ S) : x a ≤ (floor a:ℝ)+(capacity a:ℝ) := by
    by_cases h : (floor a:ℝ) < x a
    · simp only [capacity,if_pos h,Nat.cast_one]
      exact (Nat.lt_floor_add_one (x a)).le
    · simp only [capacity,if_neg h,Nat.cast_zero,add_zero]
      exact le_of_not_gt h
  have hcapac : P-(∑ a ∈ S, floor a) ≤ ∑ a ∈ S, capacity a := by
    have hh := sum_le_sum hupper
    rw [hsum,sum_add_distrib,←Nat.cast_sum,←Nat.cast_sum] at hh
    have hh' : P ≤ (∑ a ∈ S, floor a)+(∑ a ∈ S, capacity a) := by exact_mod_cast hh
    omega
  obtain ⟨inc,hinc,hincsum⟩ := split_capacity S capacity (P-∑ a ∈ S, floor a) hcapac
  refine ⟨fun a => floor a+inc a,?_,?_,?_⟩
  · rw [sum_add_distrib,hincsum]
    omega
  · intro a ha
    have hf := Nat.floor_le (hx a ha)
    have hfu := Nat.lt_floor_add_one (x a)
    have hi : inc a ≤ 1 := (hinc a ha).trans (by dsimp only [capacity]; split_ifs <;> omega)
    have hiR : (inc a:ℝ) ≤ 1 := by exact_mod_cast hi
    have hn : 0 ≤ (inc a:ℝ) := Nat.cast_nonneg _
    push_cast
    apply abs_le.mpr
    constructor <;> linarith
  · intro a ha hz
    have hf : floor a = 0 := by simp only [floor,hz,Nat.floor_zero]
    have hc : capacity a = 0 := by simp only [capacity,hf,hz,Nat.cast_zero,lt_self_iff_false,ite_false]
    have hi : inc a = 0 := by have h := hinc a ha; rw [hc] at h; omega
    simp only [hf,hi,Nat.add_zero]

lemma quantize_distribution {A : Type} (S : Finset A) (p : A → ℝ) (P : ℕ)
    (hP : 0 < P) (hp : ∀ a ∈ S, 0 ≤ p a) (hn : (∑ a ∈ S, p a) = 1) :
    ∃ m : A → ℕ, (∑ a ∈ S, m a) = P ∧
      (∀ a ∈ S, |(m a:ℝ)/P-p a| ≤ 1/P) ∧ (∀ a ∈ S, p a = 0 → m a = 0) := by
  have hPR : 0 < (P:ℝ) := by exact_mod_cast hP
  have hsum : (∑ a ∈ S, (P:ℝ)*p a) = P := by rw [←mul_sum,hn,mul_one]
  obtain ⟨m,hm,he,hz⟩ := rounded_sum S (fun a => (P:ℝ)*p a) P
    (fun a ha => mul_nonneg hPR.le (hp a ha)) hsum
  refine ⟨m,hm,?_,?_⟩
  · intro a ha
    have hid : (m a:ℝ)/P-p a = ((m a:ℝ)-(P:ℝ)*p a)/P := by field_simp
    rw [hid,abs_div,abs_of_pos hPR]
    exact div_le_div_of_nonneg_right (he a ha) hPR.le
  · intro a ha hzero
    exact hz a ha (by simp only [hzero,mul_zero])

lemma quantize_relative {A : Type} (S : Finset A) (p : A → ℝ) (P : ℕ)
    (hP : 0 < P) (hp : ∀ a ∈ S, 0 ≤ p a) (hn : (∑ a ∈ S, p a) = 1)
    (lambda alpha : ℝ) (ha : 0 ≤ alpha)
    (hmin : ∀ a ∈ S, 0 < p a → lambda ≤ p a) (hsmall : 1/(P:ℝ) ≤ alpha*lambda) :
    ∃ m : A → ℕ, (∑ a ∈ S, m a) = P ∧
      (∀ a ∈ S, (1-alpha)*p a ≤ (m a:ℝ)/P ∧ (m a:ℝ)/P ≤ (1+alpha)*p a) ∧
      (∀ a ∈ S, 0 < m a → 0 < p a) := by
  obtain ⟨m,hm,he,hz⟩ := quantize_distribution S p P hP hp hn
  refine ⟨m,hm,?_,?_⟩
  · intro a haS
    by_cases hpos : 0 < p a
    · have hb := (abs_le.mp (he a haS))
      have hs := mul_le_mul_of_nonneg_left (hmin a haS hpos) ha
      constructor <;> nlinarith
    · have hzero : p a = 0 := by have h := hp a haS; linarith
      have hmzero := hz a haS hzero
      simp only [hzero,hmzero,Nat.cast_zero,zero_div,mul_zero,le_refl,and_self]
  · intro a haS hmpos
    by_contra hnpos
    have hzero : p a = 0 := by have h := hp a haS; linarith
    have hmzero := hz a haS hzero
    omega


end PairwiseProof

-- Solutions/Sol_rounding_depth.lean

open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

def roundingDepth (lambda : ℝ) : ℕ := 10+⌈logTwo (1/lambda)⌉₊

lemma accuracy_log_ge_one (lambda : ℝ) (hl : 0 < lambda) (hu : lambda ≤ 1/2) :
    1 ≤ logTwo (1/lambda) := by
  have hinv : (2:ℝ) ≤ 1/lambda := (le_div_iff₀ hl).mpr (by linarith)
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (one_div_pos.mpr hl)).mpr
  simpa only [Real.rpow_one] using hinv

lemma roundingDepth_pos (lambda : ℝ) : 0 < roundingDepth lambda := by unfold roundingDepth; omega

lemma roundingDepth_bound (lambda : ℝ) (hl : 0 < lambda) (hu : lambda ≤ 1/2) :
    (roundingDepth lambda:ℝ) ≤ 12*logTwo (1/lambda) := by
  have hlog := accuracy_log_ge_one lambda hl hu
  have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ logTwo (1/lambda))
  simp only [roundingDepth,Nat.cast_add,Nat.cast_ofNat]
  linarith

lemma roundingDepth_precision (lambda : ℝ) (hl : 0 < lambda) (hu : lambda ≤ 1/2) :
    1/((2^roundingDepth lambda:ℕ):ℝ) ≤ (1/1000:ℝ)*lambda := by
  let L := logTwo (1/lambda)
  let t := ⌈L⌉₊
  have hpow : 1/lambda ≤ (2:ℝ)^(t:ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (one_div_pos.mpr hl)).mp
    exact Nat.le_ceil L
  have hP : ((2^roundingDepth lambda:ℕ):ℝ) = 1024*(2:ℝ)^t := by
    norm_num [roundingDepth,pow_add,t,L]
  have hpow' : 1/lambda ≤ (2:ℝ)^t := by simpa only [Real.rpow_natCast] using hpow
  have hPpos : 0 < ((2^roundingDepth lambda:ℕ):ℝ) := by positivity
  have hbig : (1000:ℝ)/lambda ≤ ((2^roundingDepth lambda:ℕ):ℝ) := by
    rw [hP]
    have hi : 0 < 1/lambda := one_div_pos.mpr hl
    rw [show (1000:ℝ)/lambda = 1000*(1/lambda) by ring]
    nlinarith
  have hh : (1000:ℝ) ≤ ((2^roundingDepth lambda:ℕ):ℝ)*lambda := (div_le_iff₀ hl).mp hbig
  apply (div_le_iff₀ hPpos).mpr
  nlinarith

end PairwiseProof

-- Solutions/Sol_grid_probability.lean

open Classical Finset
noncomputable section
namespace PairwiseProof

def localDistribution (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ) : Prop :=
  (∑ a ∈ S, p a) = 1 ∧ ∀ a ∈ S, 0 ≤ p a ∧ (0 < p a → lambda ≤ p a)

def gridDenom (lambda : ℝ) : ℕ := 2^roundingDepth lambda

lemma gridDenom_pos (lambda : ℝ) : 0 < gridDenom lambda := by unfold gridDenom; positivity

def gridNumerators (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ) (a : ℕ) : ℕ :=
  if h : 0 < lambda ∧ lambda ≤ 1/2 ∧ localDistribution lambda S p then
    if a ∈ S then
      (quantize_relative S p (gridDenom lambda) (gridDenom_pos lambda)
        (fun b hb => (h.2.2.2 b hb).1) h.2.2.1 lambda (1/1000) (by norm_num)
        (fun b hb => (h.2.2.2 b hb).2) (roundingDepth_precision lambda h.1 h.2.1)).choose a
    else 0
  else 0

def gridProbability (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ) (a : ℕ) : ℝ :=
  (gridNumerators lambda S p a:ℝ)/(gridDenom lambda:ℝ)

lemma gridNumerators_outside (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ) (a : ℕ) (ha : a ∉ S) :
    gridNumerators lambda S p a = 0 := by
  unfold gridNumerators
  split_ifs <;> simp only [ha,ite_false]

lemma gridNumerators_spec (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ)
    (hl : 0 < lambda) (hu : lambda ≤ 1/2) (hd : localDistribution lambda S p) :
    (∑ a ∈ S, gridNumerators lambda S p a) = gridDenom lambda ∧
    (∀ a ∈ S, (999/1000:ℝ)*p a ≤ gridProbability lambda S p a ∧
      gridProbability lambda S p a ≤ (1001/1000:ℝ)*p a) ∧
    (∀ a, 0 < gridNumerators lambda S p a → a ∈ S ∧ 0 < p a) := by
  let h := And.intro hl (And.intro hu hd)
  let hex := quantize_relative S p (gridDenom lambda) (gridDenom_pos lambda)
    (fun b hb => (hd.2 b hb).1) hd.1 lambda (1/1000) (by norm_num)
    (fun b hb => (hd.2 b hb).2) (roundingDepth_precision lambda hl hu)
  have he (a : ℕ) (ha : a ∈ S) : gridNumerators lambda S p a = hex.choose a := by
    unfold gridNumerators
    rw [dif_pos h,if_pos ha]
  constructor
  · rw [sum_congr rfl (fun a ha => he a ha)]
    exact hex.choose_spec.1
  constructor
  · intro a ha
    unfold gridProbability
    rw [he a ha]
    simpa only [show (1:ℝ)-1/1000 = 999/1000 by norm_num,
      show (1:ℝ)+1/1000 = 1001/1000 by norm_num] using hex.choose_spec.2.1 a ha
  · intro a hpos
    by_cases ha : a ∈ S
    · refine ⟨ha,hex.choose_spec.2.2 a ha ?_⟩
      rwa [←he a ha]
    · rw [gridNumerators_outside lambda S p a ha] at hpos
      omega

lemma gridProbability_sum (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ)
    (hl : 0 < lambda) (hu : lambda ≤ 1/2) (hd : localDistribution lambda S p) :
    (∑ a ∈ S, gridProbability lambda S p a) = 1 := by
  unfold gridProbability
  rw [←sum_div,←Nat.cast_sum,(gridNumerators_spec lambda S p hl hu hd).1]
  exact div_self (by exact_mod_cast (gridDenom_pos lambda).ne')

lemma gridProbability_nonneg (lambda : ℝ) (S : Finset ℕ) (p : ℕ → ℝ) (a : ℕ) :
    0 ≤ gridProbability lambda S p a := by unfold gridProbability; positivity

end PairwiseProof

-- Solutions/Sol_local_advance.lean

open Classical Finset
noncomputable section
namespace PairwiseProof
section Advance
variable {V K I O : Type} [Fintype V] (A : SmoothedMIS.LocalAlg K I O) (H : SimpleGraph V)

def advance (start : V → A.State) : ℕ → V → A.State
  | 0 => start
  | t+1 => fun v => A.step (advance start t v)
      ((univ.filter (H.Adj v)).val.map fun u => A.send (advance start t u))

lemma advance_congr (start start' : V → A.State) (h : ∀ v, start v = start' v) (t : ℕ) :
    ∀ v, advance A H start t v = advance A H start' t v := by
  have he : start = start' := funext h
  rw [he]
  intro v
  rfl

lemma advance_add (start : V → A.State) (p q : ℕ) : ∀ v,
    advance A H start (p+q) v = advance A H (advance A H start p) q v := by
  induction q with
  | zero => intro v; rfl
  | succ q ih =>
    intro v
    rw [show p+(q+1) = (p+q)+1 by omega,advance]
    simp only [ih]
    rfl

lemma advance_run (k : K) (ids : V → ℕ) (inp : V → I) (tape : V → ℕ → Bool) (t : ℕ) : ∀ v,
    advance A H (fun v => A.init k (ids v) (inp v) (tape v)) t v = A.run H k ids inp tape t v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    rw [advance]
    simp only [ih]
    rfl

end Advance
end PairwiseProof

-- Solutions/Sol_rounding_actions.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

inductive RoundAction where
  | gather (eta : ℝ) (Q zeta : ℕ)
  | simulate
  | coarsen (eta : ℝ) (K color : ℕ)

structure RoundData (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) where
  ownID : ℕ
  input : ObjectiveInput
  numerator : ℕ → ℕ
  denominator : ℕ
  coloringState : W.program.State
  color : ℕ

section RoundActions
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ)

abbrev RoundMessage := W.program.Msg ⊕ MarginalRecord

def dataRecord (s : RoundData W) (original : Bool) : MarginalRecord :=
  ⟨s.ownID,s.input.labels,s.numerator,s.denominator,if original then s.input.color else s.color⟩

def leftMessages (msgs : Multiset (RoundMessage W)) : Multiset W.program.Msg :=
  msgs.filterMap fun m => match m with | .inl x => some x | .inr _ => none

def rightMessages (msgs : Multiset (RoundMessage W)) : Multiset MarginalRecord :=
  msgs.filterMap fun m => match m with | .inl _ => none | .inr x => some x

def actionSend (a : RoundAction) (s : RoundData W) : RoundMessage W :=
  match a with
  | .gather .. => .inr (dataRecord W s true)
  | .simulate => .inl (W.program.send s.coloringState)
  | .coarsen .. => .inr (dataRecord W s false)

def actionStep (a : RoundAction) (s : RoundData W) (msgs : Multiset (RoundMessage W)) : RoundData W :=
  match a with
  | .gather eta Q zeta =>
    let ws := W.program.init (Q,zeta) s.ownID
      (weightsFromMessages s.input eta s.numerator s.denominator (rightMessages W msgs),s.input.color)
      (fun _ => false)
    {s with coloringState := ws, color := W.program.out ws}
  | .simulate =>
    let ws := W.program.step s.coloringState (leftMessages W msgs)
    {s with coloringState := ws, color := W.program.out ws}
  | .coarsen eta K c =>
    if s.color = c then {s with
      numerator := halfChoice s.input.labels s.numerator K
        (scoreFromMessages s.input eta s.color (rightMessages W msgs)),
      denominator := K}
    else s

structure RoundState where
  actions : List RoundAction
  data : RoundData W

def interpreter : SmoothedMIS.LocalAlg (List RoundAction) (RoundData W) (RoundData W) where
  State := RoundState W
  Msg := RoundMessage W
  rounds := List.length
  init := fun as _ inp _ => ⟨as,inp⟩
  send := fun s => match s.actions with
    | [] => .inr (dataRecord W s.data false)
    | a::_ => actionSend W a s.data
  step := fun s msgs => match s.actions with
    | [] => s
    | a::as => ⟨as,actionStep W a s.data msgs⟩
  out := RoundState.data

section Global
variable {V : Type} [Fintype V] (H : SimpleGraph V)

def globalAction (a : RoundAction) (conf : V → RoundData W) : V → RoundData W := fun v =>
  actionStep W a (conf v) ((H.neighborFinset v).val.map fun u => actionSend W a (conf u))

def foldRoundActions : List RoundAction → (V → RoundData W) → V → RoundData W
  | [],conf => conf
  | a::as,conf => foldRoundActions as (globalAction W H a conf)

lemma foldRoundActions_append (as bs : List RoundAction) (conf : V → RoundData W) :
    foldRoundActions W H (as++bs) conf = foldRoundActions W H bs (foldRoundActions W H as conf) := by
  induction as generalizing conf with
  | nil => rfl
  | cons a as ih => exact ih _

lemma interpreter_advance (as rest : List RoundAction) (conf : V → RoundData W) : ∀ v,
    advance (interpreter W) H (fun v => ⟨as++rest,conf v⟩) as.length v =
      ⟨rest,foldRoundActions W H as conf v⟩ := by
  induction as generalizing conf with
  | nil => intro v; rfl
  | cons a as ih =>
    have hfirst : advance (interpreter W) H (fun v => ⟨(a::as)++rest,conf v⟩) 1 =
        fun v => ⟨as++rest,globalAction W H a conf v⟩ := by
      funext v
      have hn : univ.filter (H.Adj v) = H.neighborFinset v := by ext u; simp
      simp only [advance,interpreter,List.cons_append]
      rw [hn]
      rfl
    intro v
    change advance (interpreter W) H (fun v => ⟨(a::as)++rest,conf v⟩) (as.length+1) v = _
    rw [show as.length+1 = 1+as.length by omega]
    have hh := advance_add (interpreter W) H (fun v => ⟨(a::as)++rest,conf v⟩) 1 as.length v
    exact hh.trans ((congrArg (fun start => advance (interpreter W) H start as.length v) hfirst).trans
      (ih (globalAction W H a conf) v))

end Global
end RoundActions
end PairwiseProof

-- Solutions/Sol_rounding_action_semantics.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Semantics
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ)
    {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ) (orig : Fin N → ℕ)

def packData (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ) : Fin N → RoundData W :=
  fun v => ⟨ids v,objectiveInput D ids orig v,(st v).1,(st v).2,ws v,col v⟩

lemma pack_record (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ)
    (v : Fin N) :
    dataRecord W (packData W D ids orig st ws col v) false = marginalRecord D ids st col v ∧
    dataRecord W (packData W D ids orig st ws col v) true = marginalRecord D ids st orig v := by
  constructor <;> rfl

lemma right_gather (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ)
    (eta : ℝ) (Q zeta : ℕ) (v : Fin N) :
    rightMessages W ((D.graph.neighborFinset v).val.map
      (fun u => actionSend W (.gather eta Q zeta) (packData W D ids orig st ws col u))) =
      marginalMessages D ids st orig v := by
  simp only [rightMessages,actionSend,Multiset.filterMap_map,Function.comp_def,
    pack_record,marginalMessages]
  exact congrFun (Multiset.filterMap_eq_map _) _

lemma right_coarsen (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ)
    (eta : ℝ) (K c : ℕ) (v : Fin N) :
    rightMessages W ((D.graph.neighborFinset v).val.map
      (fun u => actionSend W (.coarsen eta K c) (packData W D ids orig st ws col u))) =
      marginalMessages D ids st col v := by
  simp only [rightMessages,actionSend,Multiset.filterMap_map,Function.comp_def,
    pack_record,marginalMessages]
  exact congrFun (Multiset.filterMap_eq_map _) _

def stageWeights (st : NumState N) (eta : ℝ) (v : Fin N) : ℕ → ℝ :=
  weightsFromMessages (objectiveInput D ids orig v) eta (st v).1 (st v).2
    (marginalMessages D ids st orig v)

def stageColorInput (st : NumState N) (eta : ℝ) (v : Fin N) : DistributedRounding.WeightedInput :=
  (stageWeights D ids orig st eta v,orig v)

lemma global_gather (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ)
    (eta : ℝ) (Q zeta : ℕ) :
    globalAction W D.graph (.gather eta Q zeta) (packData W D ids orig st ws col) =
      packData W D ids orig st
        (fun v => W.program.init (Q,zeta) (ids v) (stageColorInput D ids orig st eta v) (fun _ => false))
        (fun v => W.program.out (W.program.init (Q,zeta) (ids v)
          (stageColorInput D ids orig st eta v) (fun _ => false))) := by
  funext v
  unfold globalAction actionStep
  rw [right_gather]
  rfl

lemma left_simulate (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ)
    (v : Fin N) :
    leftMessages W ((D.graph.neighborFinset v).val.map
      (fun u => actionSend W .simulate (packData W D ids orig st ws col u))) =
      (D.graph.neighborFinset v).val.map (fun u => W.program.send (ws u)) := by
  simp only [leftMessages,actionSend,Multiset.filterMap_map,Function.comp_def,
    packData]
  exact congrFun (Multiset.filterMap_eq_map _) _

lemma global_simulate (st : NumState N) (ws : Fin N → W.program.State) (col : Fin N → ℕ) :
    globalAction W D.graph .simulate (packData W D ids orig st ws col) =
      packData W D ids orig st (advance W.program D.graph ws 1)
        (fun v => W.program.out (advance W.program D.graph ws 1 v)) := by
  funext v
  unfold globalAction actionStep
  rw [left_simulate]
  have hn : univ.filter (D.graph.Adj v) = D.graph.neighborFinset v := by ext u; simp
  simp only [advance,packData]
  rw [hn]

lemma global_coarsen (hi : Function.Injective ids) (st : NumState N)
    (ws : Fin N → W.program.State) (col : Fin N → ℕ) (eta : ℝ) (K c : ℕ) :
    globalAction W D.graph (.coarsen eta K c) (packData W D ids orig st ws col) =
      packData W D ids orig
        (roundOne D.graph D.labels (fun v a => D.unaryUtility v a-eta*D.unaryCost v a)
          (fun v u a b => D.pairUtility v u a b-eta*D.pairCost v u a b) col K c st) ws col := by
  funext v
  unfold globalAction actionStep
  rw [right_coarsen]
  change (if col v = c then _ else _) = _
  by_cases hc : col v = c
  · rw [if_pos hc]
    have hs := halfChoice_congr (D.labels v) (st v).1 K
      (scoreFromMessages (objectiveInput D ids orig v) eta (col v) (marginalMessages D ids st col v))
      (localScore (bichromaticGraph D.graph col) D.labels (density st)
        (fun v a => D.unaryUtility v a-eta*D.unaryCost v a)
        (fun v u a b => D.pairUtility v u a b-eta*D.pairCost v u a b) v)
      (fun a ha => scoreFromMessages_correct D ids hi orig col eta st v a ha)
    simp only [packData,roundOne,if_pos hc]
    simp only [show (objectiveInput D ids orig v).labels = D.labels v from rfl]
    rw [hs]
  · simp only [packData,roundOne,if_neg hc]

end Semantics
end PairwiseProof

-- Solutions/Sol_rounding_action_folds.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

def coarseningActions (eta : ℝ) (K : ℕ) : ℕ → List RoundAction
  | 0 => []
  | c+1 => coarseningActions eta K c ++ [.coarsen eta K c]

lemma coarseningActions_length (eta : ℝ) (K M : ℕ) :
    (coarseningActions eta K M).length = M := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [coarseningActions,List.length_append,List.length_singleton,ih]

section Folds
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ)
    {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ) (orig : Fin N → ℕ)

lemma simulate_fold (st : NumState N) (ws : Fin N → W.program.State) (T : ℕ) :
    foldRoundActions W D.graph (List.replicate T RoundAction.simulate)
      (packData W D ids orig st ws (fun v => W.program.out (ws v))) =
      packData W D ids orig st (advance W.program D.graph ws T)
        (fun v => W.program.out (advance W.program D.graph ws T v)) := by
  induction T generalizing ws with
  | zero => rfl
  | succ T ih =>
    rw [List.replicate_succ,foldRoundActions,global_simulate,ih]
    have he : advance W.program D.graph (advance W.program D.graph ws 1) T =
        advance W.program D.graph ws (T+1) := by
      funext v
      exact (advance_add W.program D.graph ws 1 T v).symm.trans
        (congrArg (fun t => advance W.program D.graph ws t v) (by omega))
    rw [he]

lemma coarsening_fold (hi : Function.Injective ids) (eta : ℝ) (K M : ℕ)
    (u : Fin N → ℕ → ℕ) (ws : Fin N → W.program.State) (col : Fin N → ℕ) :
    foldRoundActions W D.graph (coarseningActions eta K M)
      (packData W D ids orig (fun v => (u v,2*K)) ws col) =
      packData W D ids orig
        (stageState D.graph D.labels D.unaryUtility D.unaryCost D.pairUtility D.pairCost eta col K u M) ws col := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [coarseningActions,foldRoundActions_append,ih]
    simp only [foldRoundActions]
    rw [global_coarsen W D ids orig hi]
    rfl

def stageActions (eta : ℝ) (Q zeta K M : ℕ) : List RoundAction :=
  [.gather eta Q zeta] ++ List.replicate (W.program.rounds (Q,zeta)) .simulate ++ coarseningActions eta K M

lemma stageActions_length (eta : ℝ) (Q zeta K M : ℕ) :
    (stageActions W eta Q zeta K M).length = 1+W.program.rounds (Q,zeta)+M := by
  simp only [stageActions,List.length_append,List.length_singleton,List.length_replicate,coarseningActions_length]

def stageColors (st : NumState N) (eta : ℝ) (Q zeta : ℕ) : Fin N → ℕ :=
  execute W D.graph (Q,zeta) ids (stageColorInput D ids orig st eta)

lemma stage_fold (hi : Function.Injective ids) (eta : ℝ) (Q zeta K M : ℕ)
    (u : Fin N → ℕ → ℕ) (ws : Fin N → W.program.State) (col : Fin N → ℕ) :
    let st : NumState N := fun v => (u v,2*K);
    let newCol := stageColors W D ids orig st eta Q zeta;
    foldRoundActions W D.graph (stageActions W eta Q zeta K M) (packData W D ids orig st ws col) =
      packData W D ids orig
        (stageState D.graph D.labels D.unaryUtility D.unaryCost D.pairUtility D.pairCost eta newCol K u M)
        (W.program.run D.graph (Q,zeta) ids (stageColorInput D ids orig st eta) (fun _ _ => false)
          (W.program.rounds (Q,zeta))) newCol := by
  dsimp only
  rw [stageActions,foldRoundActions_append,foldRoundActions_append]
  simp only [foldRoundActions]
  rw [global_gather,simulate_fold]
  have he := funext (advance_run W.program D.graph (Q,zeta) ids
    (stageColorInput D ids orig (fun v => (u v,2*K)) eta) (fun _ _ => false) (W.program.rounds (Q,zeta)))
  rw [he,coarsening_fold W D ids orig hi]
  rfl

end Folds
end PairwiseProof

-- Solutions/Sol_rounding_scalar.lean

noncomputable section
namespace PairwiseProof

lemma preprocessing_gap (U C U' C' : ℝ) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hgap : U-C ≥ (1/2)*U)
    (hlo : (999/1000:ℝ)^2*U ≤ U')
    (hup : U' ≤ (1001/1000:ℝ)^2*U)
    (hcost : C' ≤ (1001/1000:ℝ)^2*C) :
    (99/100:ℝ)*(U-C) ≤ U'-C' ∧ (1/4:ℝ)*U' ≤ U'-C' := by
  constructor <;> nlinarith

lemma potential_step (U C U' C' eta eta' delta : ℝ) (hC : 0 ≤ C)
    (hdrop : delta*(eta+eta') ≤ eta-eta')
    (hstep : U'-eta'*C' ≥ U-eta'*C-delta*(U+eta'*C)) :
    (1-delta)*(U-eta*C) ≤ U'-eta'*C' := by
  have hh := mul_le_mul_of_nonneg_right hdrop hC
  nlinarith

lemma initial_potential (U C : ℝ) (hgap : (1/4:ℝ)*U ≤ U-C) :
    (97/100:ℝ)*(U-C) ≤ U-(101/100:ℝ)*C := by nlinarith

lemma rounding_final_gap (U C U' C' Phi : ℝ) (hgap : 0 ≤ U-C)
    (hpre : (99/100:ℝ)*(U-C) ≤ U'-C')
    (hphi : (299/300:ℝ)*(97/100)*(U'-C') ≤ Phi) :
    (9/10:ℝ)*(U-C) ≤ Phi := by nlinarith

lemma bernoulli_rounding (k : ℕ) (hk : 0 < k) :
    (299/300:ℝ) ≤ (1-1/(300*(k:ℝ)))^k := by
  have hkr : 0 < (k:ℝ) := by exact_mod_cast hk
  have hdelta : (-2:ℝ) ≤ -(1/(300*(k:ℝ))) := by
    have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast hk
    have hh : 1/(300*(k:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have hb := one_add_mul_le_pow hdelta k
  have he : (k:ℝ)*(1/(300*(k:ℝ))) = 1/300 := by field_simp
  have he' : (1:ℝ)+(k:ℝ)*(-(1/(300*(k:ℝ)))) = 299/300 := by rw [mul_neg,he]; norm_num
  simpa only [he',sub_eq_add_neg] using hb

end PairwiseProof

-- Solutions/Sol_rounding_potential.lean

noncomputable section
namespace PairwiseProof

def roundingEta (k i : ℕ) : ℝ := 1+(1-(i:ℝ)/k)/100

def roundingDelta (k : ℕ) : ℝ := 1/(300*(k:ℝ))

lemma roundingDelta_bounds (k : ℕ) (hk : 0 < k) : 0 ≤ roundingDelta k ∧ roundingDelta k ≤ 1 := by
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · unfold roundingDelta; positivity
  · unfold roundingDelta
    apply (div_le_one (by positivity)).mpr
    linarith

lemma roundingEta_bounds (k i : ℕ) (hk : 0 < k) (hi : i ≤ k) :
    1 ≤ roundingEta k i ∧ roundingEta k i ≤ 101/100 := by
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hir : (i:ℝ) ≤ k := by exact_mod_cast hi
  have hdiv : (i:ℝ)/k ≤ 1 := (div_le_one hkr).mpr hir
  have hdiv0 : 0 ≤ (i:ℝ)/k := by positivity
  unfold roundingEta
  constructor <;> linarith

lemma roundingEta_start (k : ℕ) : roundingEta k 0 = 101/100 := by simp [roundingEta]; norm_num

lemma roundingEta_end (k : ℕ) (hk : 0 < k) : roundingEta k k = 1 := by
  unfold roundingEta
  rw [div_self (by exact_mod_cast hk.ne')]
  norm_num

lemma roundingEta_drop (k i : ℕ) (hk : 0 < k) :
    roundingEta k i-roundingEta k (i+1) = 3*roundingDelta k := by
  have hkr : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold roundingEta roundingDelta
  push_cast
  field_simp
  ring

lemma rounding_potential_iterate (k : ℕ) (hk : 0 < k) (U C : ℕ → ℝ)
    (hU : 0 ≤ U 0) (hgap : (1/4:ℝ)*U 0 ≤ U 0-C 0)
    (hC : ∀ i, i < k → 0 ≤ C i)
    (hstep : ∀ i, i < k → U (i+1)-roundingEta k (i+1)*C (i+1) ≥
      U i-roundingEta k (i+1)*C i-roundingDelta k*(U i+roundingEta k (i+1)*C i)) :
    (299/300:ℝ)*(97/100)*(U 0-C 0) ≤ U k-C k := by
  let Phi := fun i => U i-roundingEta k i*C i
  have hd := roundingDelta_bounds k hk
  have hphi (i : ℕ) (hi : i ≤ k) : (1-roundingDelta k)^i*Phi 0 ≤ Phi i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i < k := by omega
      have heta := (roundingEta_bounds k i hk (by omega)).2
      have heta' := (roundingEta_bounds k (i+1) hk hi).2
      have hdrop : roundingDelta k*(roundingEta k i+roundingEta k (i+1)) ≤
          roundingEta k i-roundingEta k (i+1) := by
        rw [roundingEta_drop k i hk]
        have hh := mul_le_mul_of_nonneg_left (show roundingEta k i+roundingEta k (i+1) ≤ 3 by linarith) hd.1
        linarith
      have hprog := potential_step (U i) (C i) (U (i+1)) (C (i+1))
        (roundingEta k i) (roundingEta k (i+1)) (roundingDelta k) (hC i hi') hdrop (hstep i hi')
      have hh := mul_le_mul_of_nonneg_left (ih (by omega)) (sub_nonneg.mpr hd.2)
      rw [pow_succ]
      dsimp only [Phi] at *
      nlinarith
  have hinit : (97/100:ℝ)*(U 0-C 0) ≤ Phi 0 := by
    dsimp only [Phi]
    rw [roundingEta_start]
    exact initial_potential (U 0) (C 0) hgap
  have hPhi0 : 0 ≤ Phi 0 := by linarith
  have hbernoulli : (299/300:ℝ) ≤ (1-roundingDelta k)^k := bernoulli_rounding k hk
  have hm := mul_le_mul_of_nonneg_right hbernoulli hPhi0
  have hm' := mul_le_mul_of_nonneg_left hinit (by norm_num : (0:ℝ) ≤ 299/300)
  have hfinal := hphi k le_rfl
  dsimp only [Phi] at *
  rw [roundingEta_end k hk,one_mul] at hfinal
  nlinarith

end PairwiseProof

-- Solutions/Sol_rounding_weighted_stage.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

def ColoringContract (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ) : Prop :=
  ∀ (N : ℕ) (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (Q zeta : ℕ),
    2 ≤ Q → Proper H zeta col →
    (∀ v u, 0 ≤ weights v (ids u)) →
    (∀ v u, weights v (ids u) = weights u (ids v)) →
    let out := execute W H (Q,zeta) ids (fun v => (weights v,col v))
    (∀ v, out v < B*Q) ∧
    (Q:ℝ)*DistributedRounding.monochromatic H (fun v u => weights v (ids u)) out ≤
      4*(∑ v, DistributedRounding.incident H (fun v u => weights v (ids u)) v)

section WeightedStage
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hColor : ColoringContract W B) {N : ℕ} (D : PairwiseInstance N) (lambda : ℝ)
    (hD : ValidObjective D lambda) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (orig : Fin N → ℕ) (zeta : ℕ) (hc : Proper D.graph zeta orig)

include hColor hD hi hc

lemma stage_coloring (st : NumState N) (eta : ℝ) (heta : 0 ≤ eta) (Q : ℕ) (hQ : 2 ≤ Q) :
    let col := stageColors W D ids orig st eta Q zeta;
    (∀ v, col v < B*Q) ∧
    (Q:ℝ)*(∑ v, ∑ u ∈ D.graph.neighborFinset v, if col u = col v then
      pairWeights D.graph D.labels (density st)
        (fun v u a b => D.pairUtility v u a b+eta*D.pairCost v u a b) v u else 0) ≤
      4*(∑ v, ∑ u ∈ D.graph.neighborFinset v,
        pairWeights D.graph D.labels (density st)
          (fun v u a b => D.pairUtility v u a b+eta*D.pairCost v u a b) v u) := by
  have hw (v u : Fin N) : stageWeights D ids orig st eta v (ids u) =
      pairWeights D.graph D.labels (density st)
        (fun v u a b => D.pairUtility v u a b+eta*D.pairCost v u a b) v u :=
    weightsFromMessages_correct D ids hi orig orig eta st v u
  have hn (v u : Fin N) : 0 ≤ stageWeights D ids orig st eta v (ids u) := by
    rw [hw]
    apply pairWeights_nonneg _ _ _ _ (density_nonneg st)
    intro v u a b
    exact add_nonneg (hD.2.2.2.2.2 v u a b).1 (mul_nonneg heta (hD.2.2.2.2.2 v u a b).2)
  have hs (v u : Fin N) : stageWeights D ids orig st eta v (ids u) =
      stageWeights D ids orig st eta u (ids v) := by
    rw [hw,hw]
    exact pairWeights_symm _ _ _ _ v u
  have hh := hColor N D.graph ids (stageWeights D ids orig st eta) orig Q zeta hQ hc hn hs
  change (∀ v, stageColors W D ids orig st eta Q zeta v < B*Q) ∧ _ at hh
  refine ⟨hh.1,?_⟩
  unfold stageColors stageColorInput
  simpa only [DistributedRounding.monochromatic,DistributedRounding.incident,hw,
    stageColors,stageColorInput] using hh.2

lemma stage_guarantee (K : ℕ) (hK : 0 < K) (u : Fin N → ℕ → ℕ)
    (hu : ∀ v, (∑ a ∈ D.labels v, u v a) = 2*K)
    (eta : ℝ) (heta : 0 ≤ eta) (Q : ℕ) (hQ : 2 ≤ Q) :
    let st : NumState N := fun v => (u v,2*K);
    let col := stageColors W D ids orig st eta Q zeta;
    let newSt := stageState D.graph D.labels D.unaryUtility D.unaryCost
      D.pairUtility D.pairCost eta col K u (B*Q);
    (∀ v, (newSt v).2 = K ∧ (∑ a ∈ D.labels v, (newSt v).1 a) = K ∧
      ∀ a, (newSt v).1 a ≤ u v a) ∧
    -(12:ℝ)*(mean D.graph D.labels (density st) D.unaryUtility D.pairUtility+
      eta*mean D.graph D.labels (density st) D.unaryCost D.pairCost) ≤
      (Q:ℝ)*((mean D.graph D.labels (density newSt) D.unaryUtility D.pairUtility-
        eta*mean D.graph D.labels (density newSt) D.unaryCost D.pairCost)-
        (mean D.graph D.labels (density st) D.unaryUtility D.pairUtility-
        eta*mean D.graph D.labels (density st) D.unaryCost D.pairCost)) := by
  have hh := stage_coloring W B hColor D lambda hD ids hi orig zeta hc
    (fun v => (u v,2*K)) eta heta Q hQ
  refine ⟨stageState_grid D.graph D.labels D.unaryUtility D.unaryCost
    D.pairUtility D.pairCost eta _ K u (B*Q) hK hu hh.1,?_⟩
  exact stageState_loss D.graph D.labels D.unaryUtility D.unaryCost
    D.pairUtility D.pairCost eta heta _ K u (B*Q) Q hK hu
    (fun v a => (hD.2.2.2.2.1 v a).1) (fun v a => (hD.2.2.2.2.1 v a).2)
    (fun v u a b => (hD.2.2.2.2.2 v u a b).1)
    (fun v u a b => (hD.2.2.2.2.2 v u a b).2) hh.2

end WeightedStage
end PairwiseProof

-- Solutions/Sol_pairwise_preprocess.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

lemma preprocess_objective {N : ℕ} (D : PairwiseInstance N) (lambda : ℝ)
    (hD : ValidObjective D lambda)
    (hgap : finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥
      (1/2)*finiteExpectation D (utility D)) :
    let m := fun v => gridNumerators lambda (D.labels v) (D.probability v)
    let q := fun v => gridProbability lambda (D.labels v) (D.probability v)
    (∀ v, (∑ a ∈ D.labels v, m v a) = gridDenom lambda) ∧
    (∀ v, (∑ a ∈ D.labels v, q v a) = 1) ∧
    (∀ v a, 0 ≤ q v a) ∧
    (∀ v a, a ∉ D.labels v → q v a = 0) ∧
    (∀ v a, 0 < m v a → a ∈ D.labels v ∧ 0 < D.probability v a) ∧
    (99/100:ℝ)*(finiteExpectation D (utility D)-finiteExpectation D (cost D)) ≤
      mean D.graph D.labels q D.unaryUtility D.pairUtility-
        mean D.graph D.labels q D.unaryCost D.pairCost ∧
    (1/4:ℝ)*mean D.graph D.labels q D.unaryUtility D.pairUtility ≤
      mean D.graph D.labels q D.unaryUtility D.pairUtility-
        mean D.graph D.labels q D.unaryCost D.pairCost := by
  let q := fun v => gridProbability lambda (D.labels v) (D.probability v)
  have hl := hD.1
  have hu := hD.2.1
  have hn := hD.2.2.1
  have hp := hD.2.2.2.1
  have hlocal (v : Fin N) : localDistribution lambda (D.labels v) (D.probability v) :=
    ⟨hn v,fun a ha => ⟨(hp v a).1,(hp v a).2.2⟩⟩
  have hspec (v : Fin N) := gridNumerators_spec lambda (D.labels v) (D.probability v) hl hu (hlocal v)
  have hq : ∀ v a, 0 ≤ q v a := fun v a => gridProbability_nonneg lambda _ _ a
  have hout (v : Fin N) (a : ℕ) (ha : a ∉ D.labels v) : q v a = 0 := by
    unfold q gridProbability
    rw [gridNumerators_outside lambda (D.labels v) (D.probability v) a ha]
    simp only [Nat.cast_zero,zero_div]
  have hinterval (v : Fin N) (a : ℕ) :
      (999/1000:ℝ)*D.probability v a ≤ q v a ∧ q v a ≤ (1001/1000:ℝ)*D.probability v a := by
    by_cases ha : a ∈ D.labels v
    · exact (hspec v).2.1 a ha
    · rw [(hp v a).2.1 ha,hout v a ha]
      simp only [mul_zero,le_refl,and_self]
  have hU := mean_interval D.graph D.labels D.probability D.unaryUtility D.pairUtility q
    (999/1000) (1001/1000) (by norm_num) (by norm_num) (by norm_num)
    (fun v a => (hp v a).1) hq (fun v a => (hinterval v a).1) (fun v a => (hinterval v a).2)
    (fun v a => (hD.2.2.2.2.1 v a).1) (fun v w a b => (hD.2.2.2.2.2 v w a b).1)
  have hC := mean_interval D.graph D.labels D.probability D.unaryCost D.pairCost q
    (999/1000) (1001/1000) (by norm_num) (by norm_num) (by norm_num)
    (fun v a => (hp v a).1) hq (fun v a => (hinterval v a).1) (fun v a => (hinterval v a).2)
    (fun v a => (hD.2.2.2.2.1 v a).2) (fun v w a b => (hD.2.2.2.2.2 v w a b).2)
  have hUnonneg := mean_nonneg D.graph D.labels D.probability D.unaryUtility D.pairUtility
    (fun v a => (hp v a).1) (fun v a => (hD.2.2.2.2.1 v a).1)
    (fun v w a b => (hD.2.2.2.2.2 v w a b).1)
  have hCnonneg := mean_nonneg D.graph D.labels D.probability D.unaryCost D.pairCost
    (fun v a => (hp v a).1) (fun v a => (hD.2.2.2.2.1 v a).2)
    (fun v w a b => (hD.2.2.2.2.2 v w a b).2)
  rw [finiteExpectation_utility D hn,finiteExpectation_cost D hn] at hgap
  have hresult := preprocessing_gap _ _ _ _ hUnonneg hCnonneg hgap hU.1 hU.2 hC.2
  refine ⟨fun v => (hspec v).1,fun v => gridProbability_sum lambda _ _ hl hu (hlocal v),hq,hout,
    fun v a => (hspec v).2.2 a,?_,hresult.2⟩
  rw [finiteExpectation_utility D hn,finiteExpectation_cost D hn]
  exact hresult.1

end PairwiseProof

-- Solutions/Sol_rounding_sequence.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

def roundingQ (k : ℕ) : ℕ := 3600*k

def remainingGrid (k i : ℕ) : ℕ := 2^(k-i)

lemma remainingGrid_pos (k i : ℕ) : 0 < remainingGrid k i := by unfold remainingGrid; positivity

lemma remainingGrid_step (k i : ℕ) (hi : i < k) : remainingGrid k i = 2*remainingGrid k (i+1) := by
  unfold remainingGrid
  rw [show k-i = (k-(i+1))+1 by omega,pow_succ]
  omega

section Sequence
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ) (orig : Fin N → ℕ)
    (k zeta : ℕ)

def nextStage (i : ℕ) (u : Fin N → ℕ → ℕ) : NumState N :=
  let K := remainingGrid k (i+1)
  let eta := roundingEta k (i+1)
  let col := stageColors W D ids orig (fun v => (u v,2*K)) eta (roundingQ k) zeta
  stageState D.graph D.labels D.unaryUtility D.unaryCost D.pairUtility D.pairCost
    eta col K u (B*roundingQ k)

def sequenceNums (u0 : Fin N → ℕ → ℕ) : ℕ → Fin N → ℕ → ℕ
  | 0 => u0
  | i+1 => fun v => (nextStage W B D ids orig k zeta i (sequenceNums u0 i) v).1

def sequenceState (u0 : Fin N → ℕ → ℕ) (i : ℕ) : NumState N :=
  fun v => (sequenceNums W B D ids orig k zeta u0 i v,remainingGrid k i)

variable (hColor : ColoringContract W B) (lambda : ℝ) (hD : ValidObjective D lambda)
    (hi : Function.Injective ids) (hc : Proper D.graph zeta orig) (hk : 0 < k)

include hColor hD hi hc hk

lemma sequence_grid (u0 : Fin N → ℕ → ℕ)
    (h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0) (i : ℕ) (hi' : i ≤ k) :
    (∀ v, (∑ a ∈ D.labels v, sequenceNums W B D ids orig k zeta u0 i v a) = remainingGrid k i) ∧
    (∀ v a, sequenceNums W B D ids orig k zeta u0 i v a ≤ u0 v a) := by
  induction i with
  | zero => exact ⟨h0,fun _ _ => le_refl _⟩
  | succ i ih =>
    have hil : i < k := by omega
    have hp := ih (by omega)
    have hn (v : Fin N) : (∑ a ∈ D.labels v, sequenceNums W B D ids orig k zeta u0 i v a) =
        2*remainingGrid k (i+1) := (hp.1 v).trans (remainingGrid_step k i hil)
    have heta : 0 ≤ roundingEta k (i+1) := le_trans (by norm_num) (roundingEta_bounds k (i+1) hk hi').1
    have hQ : 2 ≤ roundingQ k := by unfold roundingQ; omega
    have hh := stage_guarantee W B hColor D lambda hD ids hi orig zeta hc
      (remainingGrid k (i+1)) (remainingGrid_pos k (i+1)) _ hn
      (roundingEta k (i+1)) heta (roundingQ k) hQ
    refine ⟨fun v => (hh.1 v).2.1,fun v a => le_trans ((hh.1 v).2.2 a) (hp.2 v a)⟩

lemma sequence_next (u0 : Fin N → ℕ → ℕ)
    (h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0) (i : ℕ) (hil : i < k) :
    nextStage W B D ids orig k zeta i (sequenceNums W B D ids orig k zeta u0 i) =
      sequenceState W B D ids orig k zeta u0 (i+1) := by
  have hg := sequence_grid W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 i (by omega)
  have hn (v : Fin N) := (hg.1 v).trans (remainingGrid_step k i hil)
  have heta : 0 ≤ roundingEta k (i+1) := le_trans (by norm_num) (roundingEta_bounds k (i+1) hk (by omega)).1
  have hQ : 2 ≤ roundingQ k := by unfold roundingQ; omega
  have hh := stage_guarantee W B hColor D lambda hD ids hi orig zeta hc
    (remainingGrid k (i+1)) (remainingGrid_pos k (i+1)) _ hn
    (roundingEta k (i+1)) heta (roundingQ k) hQ
  funext v
  apply Prod.ext
  · rfl
  · exact (hh.1 v).1

lemma sequence_loss (u0 : Fin N → ℕ → ℕ)
    (h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0) (i : ℕ) (hil : i < k) :
    let p := density (sequenceState W B D ids orig k zeta u0 i)
    let q := density (sequenceState W B D ids orig k zeta u0 (i+1))
    mean D.graph D.labels q D.unaryUtility D.pairUtility-
      roundingEta k (i+1)*mean D.graph D.labels q D.unaryCost D.pairCost ≥
    mean D.graph D.labels p D.unaryUtility D.pairUtility-
      roundingEta k (i+1)*mean D.graph D.labels p D.unaryCost D.pairCost-
      roundingDelta k*(mean D.graph D.labels p D.unaryUtility D.pairUtility+
        roundingEta k (i+1)*mean D.graph D.labels p D.unaryCost D.pairCost) := by
  have hg := sequence_grid W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 i (by omega)
  have hn (v : Fin N) := (hg.1 v).trans (remainingGrid_step k i hil)
  have heta : 0 ≤ roundingEta k (i+1) := le_trans (by norm_num) (roundingEta_bounds k (i+1) hk (by omega)).1
  have hQ : 2 ≤ roundingQ k := by unfold roundingQ; omega
  have hh := (stage_guarantee W B hColor D lambda hD ids hi orig zeta hc
    (remainingGrid k (i+1)) (remainingGrid_pos k (i+1)) _ hn
    (roundingEta k (i+1)) heta (roundingQ k) hQ).2
  have hp : (fun v => (sequenceNums W B D ids orig k zeta u0 i v,2*remainingGrid k (i+1))) =
      sequenceState W B D ids orig k zeta u0 i := by
    funext v
    exact Prod.ext rfl (remainingGrid_step k i hil).symm
  change -(12:ℝ)*_ ≤ (roundingQ k:ℝ)*_ at hh
  change _ ≤ _
  change -(12:ℝ)*_ ≤ (roundingQ k:ℝ)*((mean D.graph D.labels
    (density (nextStage W B D ids orig k zeta i (sequenceNums W B D ids orig k zeta u0 i))) _ _-
    _*mean D.graph D.labels (density (nextStage W B D ids orig k zeta i
      (sequenceNums W B D ids orig k zeta u0 i))) _ _)-_) at hh
  rw [sequence_next W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 i hil,hp] at hh
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have he : roundingDelta k = 12/(roundingQ k:ℝ) := by
    unfold roundingDelta roundingQ
    push_cast
    field_simp
    ring
  rw [he]
  have hQr : (0:ℝ) < roundingQ k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hQ)
  have hd := (div_le_iff₀ hQr).mpr (hh.trans_eq (mul_comm _ _))
  simp only [neg_mul,neg_div,mul_div_right_comm] at hd
  linarith only [hd]

end Sequence
end PairwiseProof

-- Solutions/Sol_rounding_plan.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Plan
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B k zeta : ℕ)

def stageInstruction (i : ℕ) : List RoundAction :=
  stageActions W (roundingEta k (i+1)) (roundingQ k) zeta (remainingGrid k (i+1)) (B*roundingQ k)

def planPrefix : ℕ → List RoundAction
  | 0 => []
  | i+1 => planPrefix i ++ stageInstruction W B k zeta i

def cycleLength : ℕ := 1+W.program.rounds (roundingQ k,zeta)+B*roundingQ k

lemma stageInstruction_length (i : ℕ) : (stageInstruction W B k zeta i).length = cycleLength W B k zeta :=
  stageActions_length W _ _ _ _ _

lemma planPrefix_length (i : ℕ) : (planPrefix W B k zeta i).length = i*cycleLength W B k zeta := by
  induction i with
  | zero => simp only [planPrefix,List.length_nil,Nat.zero_mul]
  | succ i ih =>
    rw [planPrefix,List.length_append,ih,stageInstruction_length,Nat.succ_mul]

end Plan
section PlanCorrect
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    {N : ℕ} (D : PairwiseInstance N) (ids : Fin N → ℕ) (orig : Fin N → ℕ) (k zeta : ℕ)
    (hColor : ColoringContract W B) (lambda : ℝ) (hD : ValidObjective D lambda)
    (hi : Function.Injective ids) (hc : Proper D.graph zeta orig) (hk : 0 < k)
include hColor hD hi hc hk

lemma planPrefix_frame (u0 : Fin N → ℕ → ℕ)
    (h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0)
    (ws0 : Fin N → W.program.State) (col0 : Fin N → ℕ) (i : ℕ) (hil : i ≤ k) :
    ∃ ws col,
      foldRoundActions W D.graph (planPrefix W B k zeta i)
        (packData W D ids orig (fun v => (u0 v,remainingGrid k 0)) ws0 col0) =
        packData W D ids orig (sequenceState W B D ids orig k zeta u0 i) ws col := by
  induction i with
  | zero => exact ⟨ws0,col0,rfl⟩
  | succ i ih =>
    obtain ⟨ws,col,he⟩ := ih (by omega)
    rw [planPrefix,foldRoundActions_append,he]
    have hst : sequenceState W B D ids orig k zeta u0 i =
        fun v => (sequenceNums W B D ids orig k zeta u0 i v,2*remainingGrid k (i+1)) := by
      funext v
      exact Prod.ext rfl (remainingGrid_step k i (by omega))
    rw [hst,stageInstruction,stage_fold W D ids orig hi]
    let base : NumState N := fun v => (sequenceNums W B D ids orig k zeta u0 i v,2*remainingGrid k (i+1))
    let eta := roundingEta k (i+1)
    refine ⟨W.program.run D.graph (roundingQ k,zeta) ids (stageColorInput D ids orig base eta)
      (fun _ _ => false) (W.program.rounds (roundingQ k,zeta)),
      stageColors W D ids orig base eta (roundingQ k) zeta,?_⟩
    have hn := sequence_next W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 i (by omega)
    change packData W D ids orig
      (nextStage W B D ids orig k zeta i (sequenceNums W B D ids orig k zeta u0 i)) _ _ = _
    rw [hn]

end PlanCorrect
end PairwiseProof

-- Solutions/Sol_rounding_output.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

def selectedLabel (S : Finset ℕ) (u : ℕ → ℕ) : ℕ :=
  if h : ∃ a ∈ S, 0 < u a then h.choose else 0

lemma selectedLabel_spec (S : Finset ℕ) (u : ℕ → ℕ) (hn : (∑ a ∈ S, u a) = 1) :
    selectedLabel S u ∈ S ∧ u (selectedLabel S u) = 1 ∧
      ∀ a ∈ S, u a = if a = selectedLabel S u then 1 else 0 := by
  have hex : ∃ a ∈ S, 0 < u a := by
    by_contra h
    have hz : ∀ a ∈ S, u a = 0 := by
      intro a ha
      by_contra hne
      exact h ⟨a,ha,by omega⟩
    have hs := sum_eq_zero hz
    omega
  have hs : selectedLabel S u ∈ S ∧ 0 < u (selectedLabel S u) := by
    unfold selectedLabel
    rw [dif_pos hex]
    exact hex.choose_spec
  have hle : u (selectedLabel S u) ≤ 1 := by
    rw [←hn]
    exact single_le_sum (fun a _ => Nat.zero_le (u a)) hs.1
  have hone : u (selectedLabel S u) = 1 := by omega
  refine ⟨hs.1,hone,?_⟩
  intro a ha
  by_cases he : a = selectedLabel S u
  · rw [if_pos he,he,hone]
  · rw [if_neg he]
    have herase := sum_erase_add S u hs.1
    have hz : (∑ b ∈ S.erase (selectedLabel S u), u b) = 0 := by omega
    have hh := single_le_sum (fun b _ => Nat.zero_le (u b)) (mem_erase.mpr ⟨he,ha⟩)
    omega

lemma dirac_mean {N : ℕ} (H : SimpleGraph (Fin N)) (labels : Fin N → Finset ℕ)
    (p : Fin N → ℕ → ℝ) (U : Fin N → ℕ → ℝ) (B : Fin N → Fin N → ℕ → ℕ → ℝ)
    (s : Fin N → ℕ) (hs : ∀ v, s v ∈ labels v)
    (hp : ∀ v a, a ∈ labels v → p v a = if a = s v then 1 else 0) :
    mean H labels p U B = (∑ v, U v (s v))+
      ∑ v, ∑ w ∈ H.neighborFinset v, B v w (s v) (s w) := by
  have hunary (v : Fin N) : (∑ a ∈ labels v, p v a*U v a) = U v (s v) := by
    rw [sum_eq_single (s v)]
    · rw [hp v (s v) (hs v),if_pos rfl,one_mul]
    · intro a ha he
      rw [hp v a ha,if_neg he,zero_mul]
    · exact fun h => (h (hs v)).elim
  have hpair (v w : Fin N) :
      (∑ a ∈ labels v, ∑ b ∈ labels w, p v a*p w b*B v w a b) = B v w (s v) (s w) := by
    rw [sum_eq_single (s v)]
    · rw [sum_eq_single (s w)]
      · simp only [hp v (s v) (hs v),hp w (s w) (hs w),ite_true,one_mul]
      · intro b hb he
        rw [hp w b hb,if_neg he,mul_zero,zero_mul]
      · exact fun h => (h (hs w)).elim
    · intro a ha he
      rw [hp v a ha,if_neg he]
      simp only [zero_mul,sum_const_zero]
    · exact fun h => (h (hs v)).elim
  simp only [mean,hunary,hpair]

end PairwiseProof

-- Solutions/Sol_rounding_protocol.lean

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof
section Protocol
variable (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)

def initialRoundData (lambda : ℝ) (zeta id : ℕ) (inp : ObjectiveInput) : RoundData W :=
  ⟨id,inp,gridNumerators lambda inp.labels inp.probability,gridDenom lambda,
    W.program.init (roundingQ (roundingDepth lambda),zeta) id (fun _ => 0,inp.color) (fun _ => false),inp.color⟩

def roundingProgram : Deterministic (ℝ × ℕ) ObjectiveInput ℕ where
  program := {
    State := RoundState W
    Msg := RoundMessage W
    rounds := fun k => (planPrefix W B (roundingDepth k.1) k.2 (roundingDepth k.1)).length
    init := fun k id inp _ =>
      ⟨planPrefix W B (roundingDepth k.1) k.2 (roundingDepth k.1),initialRoundData W k.1 k.2 id inp⟩
    send := (interpreter W).send
    step := (interpreter W).step
    out := fun s => selectedLabel s.data.input.labels s.data.numerator }
  tape_independent := by intros; rfl

lemma roundingProgram_run {V : Type} [Fintype V] (H : SimpleGraph V) (lambda : ℝ) (zeta : ℕ)
    (ids : V → ℕ) (inp : V → ObjectiveInput) (t : ℕ) : ∀ v,
    (roundingProgram W B).program.run H (lambda,zeta) ids inp (fun _ _ => false) t v =
      advance (interpreter W) H (fun v =>
        ⟨planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda),
          initialRoundData W lambda zeta (ids v) (inp v)⟩) t v := by
  induction t with
  | zero => intro v; rfl
  | succ t ih =>
    intro v
    conv_lhs => rw [SmoothedMIS.LocalAlg.run]
    conv_rhs => unfold advance
    simp only [ih]
    rfl

lemma roundingProgram_end {V : Type} [Fintype V] (H : SimpleGraph V) (lambda : ℝ) (zeta : ℕ)
    (ids : V → ℕ) (inp : V → ObjectiveInput) (v : V) :
    (roundingProgram W B).program.run H (lambda,zeta) ids inp (fun _ _ => false)
      ((roundingProgram W B).program.rounds (lambda,zeta)) v =
      ⟨[],foldRoundActions W H (planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda))
        (fun v => initialRoundData W lambda zeta (ids v) (inp v)) v⟩ := by
  rw [roundingProgram_run]
  change @Eq (RoundState W)
    (advance (interpreter W) H (fun v =>
      ⟨planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda),
        initialRoundData W lambda zeta (ids v) (inp v)⟩)
      (planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda)).length v)
    ⟨[],foldRoundActions W H (planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda))
      (fun v => initialRoundData W lambda zeta (ids v) (inp v)) v⟩
  simpa only [List.append_nil] using interpreter_advance W H (planPrefix W B (roundingDepth lambda) zeta (roundingDepth lambda)) []
    (fun v => initialRoundData W lambda zeta (ids v) (inp v)) v

end Protocol
end PairwiseProof

-- Solutions/Sol_rounding_runtime.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

lemma rounding_runtime (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hTime : ∀ Q zeta, 2 ≤ Q → W.program.rounds (Q,zeta) ≤ B*(Q+logStar zeta))
    (lambda : ℝ) (zeta : ℕ) (hl : 0 < lambda) (hu : lambda ≤ 1/2) :
    (roundingProgram W B).program.rounds (lambda,zeta) ≤ budget (10000000*((B:ℝ)+1))
      ((logTwo (1/lambda))^2+logTwo (1/lambda)*(logStar zeta:ℝ)) := by
  let k := roundingDepth lambda
  let L := logTwo (1/lambda)
  let S : ℝ := logStar zeta
  have hk : 0 < k := roundingDepth_pos lambda
  have hQ : 2 ≤ roundingQ k := by unfold roundingQ; omega
  have hT := hTime (roundingQ k) zeta hQ
  have hTr : (W.program.rounds (roundingQ k,zeta):ℝ) ≤ (B:ℝ)*(3600*(k:ℝ)+S) := by
    have hh : (W.program.rounds (roundingQ k,zeta):ℝ) ≤ (B:ℝ)*((roundingQ k:ℝ)+(logStar zeta:ℝ)) := by exact_mod_cast hT
    simpa only [roundingQ,Nat.cast_mul,Nat.cast_ofNat,S] using hh
  have hkbound : (k:ℝ) ≤ 12*L := roundingDepth_bound lambda hl hu
  have hL : 1 ≤ L := accuracy_log_ge_one lambda hl hu
  have hL0 : 0 ≤ L := by linarith
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hB : 0 ≤ (B:ℝ) := Nat.cast_nonneg _
  have hin : 1+(W.program.rounds (roundingQ k,zeta):ℝ)+(B:ℝ)*(3600*(k:ℝ)) ≤
      ((B:ℝ)+1)*(86401*L+S) := by
    have hh := mul_le_mul_of_nonneg_left hkbound hB
    nlinarith
  have hreal : ((roundingProgram W B).program.rounds (lambda,zeta):ℝ) ≤
      10000000*((B:ℝ)+1)*(L^2+L*S) := by
    change ((planPrefix W B k zeta k).length:ℝ) ≤ _
    rw [planPrefix_length]
    simp only [cycleLength,roundingQ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    calc
      (k:ℝ)*(1+(W.program.rounds (3600*k,zeta):ℝ)+(B:ℝ)*(3600*(k:ℝ))) ≤
          (12*L)*(((B:ℝ)+1)*(86401*L+S)) :=
        mul_le_mul hkbound hin (by positivity) (by positivity)
      _ = ((B:ℝ)+1)*(1036812*L^2+12*(L*S)) := by ring
      _ ≤ ((B:ℝ)+1)*(10000000*(L^2+L*S)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [sq_nonneg L,mul_nonneg hL0 hS]
      _ = _ := by ring
  have hh := le_trans hreal (Nat.le_ceil (10000000*((B:ℝ)+1)*(L^2+L*S)))
  exact_mod_cast hh

end PairwiseProof

-- Solutions/Sol_rounding_sequence_value.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

lemma sequence_value (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hColor : ColoringContract W B) {N : ℕ} (D : PairwiseInstance N) (lambda : ℝ)
    (hD : ValidObjective D lambda) (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (orig : Fin N → ℕ) (zeta : ℕ) (hc : Proper D.graph zeta orig)
    (hgap : finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥
      (1/2)*finiteExpectation D (utility D)) :
    let k := roundingDepth lambda
    let u0 := fun v => gridNumerators lambda (D.labels v) (D.probability v)
    let s := fun v => selectedLabel (D.labels v) (sequenceNums W B D ids orig k zeta u0 k v)
    (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
    utility D s-cost D s ≥ (9/10)*(finiteExpectation D (utility D)-finiteExpectation D (cost D)) := by
  let k := roundingDepth lambda
  let u0 := fun v => gridNumerators lambda (D.labels v) (D.probability v)
  let q0 := fun v => gridProbability lambda (D.labels v) (D.probability v)
  let st := sequenceState W B D ids orig k zeta u0
  let s := fun v => selectedLabel (D.labels v) (sequenceNums W B D ids orig k zeta u0 k v)
  have hk : 0 < k := roundingDepth_pos lambda
  have hpre := preprocess_objective D lambda hD hgap
  have h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0 := hpre.1
  have hgrid := sequence_grid W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 k le_rfl
  have hn (v : Fin N) : (∑ a ∈ D.labels v, sequenceNums W B D ids orig k zeta u0 k v a) = 1 := by
    simpa only [remainingGrid,Nat.sub_self,pow_zero] using hgrid.1 v
  have hsel (v : Fin N) := selectedLabel_spec (D.labels v) _ (hn v)
  have hs : ∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v) := by
    intro v
    have hpos : 0 < u0 v (s v) := lt_of_lt_of_le (by rw [(hsel v).2.1]; omega) (hgrid.2 v (s v))
    exact hpre.2.2.2.2.1 v (s v) hpos
  have hdirac (v : Fin N) (a : ℕ) (ha : a ∈ D.labels v) :
      density (st k) v a = if a = s v then 1 else 0 := by
    change (sequenceNums W B D ids orig k zeta u0 k v a:ℝ)/(remainingGrid k k:ℝ) = _
    rw [(hsel v).2.2 a ha]
    simp only [remainingGrid,Nat.sub_self,pow_zero,Nat.cast_one,div_one]
    split_ifs <;> norm_num
  have hUfinal : mean D.graph D.labels (density (st k)) D.unaryUtility D.pairUtility = utility D s :=
    dirac_mean D.graph D.labels (density (st k)) D.unaryUtility D.pairUtility s (fun v => (hs v).1) hdirac
  have hCfinal : mean D.graph D.labels (density (st k)) D.unaryCost D.pairCost = cost D s :=
    dirac_mean D.graph D.labels (density (st k)) D.unaryCost D.pairCost s (fun v => (hs v).1) hdirac
  let U := fun i => mean D.graph D.labels (density (st i)) D.unaryUtility D.pairUtility
  let C := fun i => mean D.graph D.labels (density (st i)) D.unaryCost D.pairCost
  have hU (i : ℕ) : 0 ≤ U i := mean_nonneg D.graph D.labels _ _ _ (density_nonneg _)
    (fun v a => (hD.2.2.2.2.1 v a).1) (fun v u a b => (hD.2.2.2.2.2 v u a b).1)
  have hC (i : ℕ) : 0 ≤ C i := mean_nonneg D.graph D.labels _ _ _ (density_nonneg _)
    (fun v a => (hD.2.2.2.2.1 v a).2) (fun v u a b => (hD.2.2.2.2.2 v u a b).2)
  have hstart : density (st 0) = q0 := by rfl
  have hpreGap : (99/100:ℝ)*(finiteExpectation D (utility D)-finiteExpectation D (cost D)) ≤ U 0-C 0 := by
    dsimp only [U,C]
    rw [hstart]
    exact hpre.2.2.2.2.2.1
  have hinitGap : (1/4:ℝ)*U 0 ≤ U 0-C 0 := by
    dsimp only [U,C]
    rw [hstart]
    exact hpre.2.2.2.2.2.2
  have hstep (i : ℕ) (hil : i < k) : U (i+1)-roundingEta k (i+1)*C (i+1) ≥
      U i-roundingEta k (i+1)*C i-roundingDelta k*(U i+roundingEta k (i+1)*C i) :=
    sequence_loss W B D ids orig k zeta hColor lambda hD hi hc hk u0 h0 i hil
  have hphi := rounding_potential_iterate k hk U C (hU 0) hinitGap (fun i _ => hC i) hstep
  have hOrigU : 0 ≤ finiteExpectation D (utility D) := by
    rw [finiteExpectation_utility D hD.2.2.1]
    exact mean_nonneg D.graph D.labels _ _ _ (fun v a => (hD.2.2.2.1 v a).1)
      (fun v a => (hD.2.2.2.2.1 v a).1) (fun v u a b => (hD.2.2.2.2.2 v u a b).1)
  have hOrigGap : 0 ≤ finiteExpectation D (utility D)-finiteExpectation D (cost D) := by linarith
  have hfinal := rounding_final_gap _ _ (U 0) (C 0) (U k-C k) hOrigGap hpreGap hphi
  refine ⟨hs,?_⟩
  dsimp only [U,C] at hfinal
  rw [hUfinal,hCfinal] at hfinal
  exact hfinal

end PairwiseProof

-- Solutions/Sol_rounding_correct.lean

open Classical Finset
open FasterDistributedMatching.ApproximateMatching
noncomputable section
namespace PairwiseProof

lemma rounding_correct (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hColor : ColoringContract W B) (N : ℕ) (D : PairwiseInstance N) (lambda : ℝ) (zeta : ℕ)
    (orig : Fin N → ℕ) (hD : ValidObjective D lambda) (hc : Proper D.graph zeta orig)
    (hgap : finiteExpectation D (utility D)-finiteExpectation D (cost D) ≥
      (1/2)*finiteExpectation D (utility D)) (ids : Fin N → ℕ) (hi : Function.Injective ids) :
    let s := execute (roundingProgram W B) D.graph (lambda,zeta) ids (objectiveInput D ids orig)
    (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
      utility D s-cost D s ≥ (9/10)*(finiteExpectation D (utility D)-finiteExpectation D (cost D)) := by
  let k := roundingDepth lambda
  let u0 := fun v => gridNumerators lambda (D.labels v) (D.probability v)
  let ws0 := fun v => W.program.init (roundingQ k,zeta) (ids v) (fun _ => 0,orig v) (fun _ => false)
  have hpre := preprocess_objective D lambda hD hgap
  have h0 : ∀ v, (∑ a ∈ D.labels v, u0 v a) = remainingGrid k 0 := hpre.1
  have hinit : (fun v => initialRoundData W lambda zeta (ids v) (objectiveInput D ids orig v)) =
      packData W D ids orig (fun v => (u0 v,remainingGrid k 0)) ws0 orig := by
    funext v
    rfl
  obtain ⟨ws,col,hframe⟩ := planPrefix_frame W B D ids orig k zeta hColor lambda hD hi hc
    (roundingDepth_pos lambda) u0 h0 ws0 orig k le_rfl
  have he : foldRoundActions W D.graph (planPrefix W B k zeta k)
      (fun v => initialRoundData W lambda zeta (ids v) (objectiveInput D ids orig v)) =
      packData W D ids orig (sequenceState W B D ids orig k zeta u0 k) ws col := by
    rw [hinit]
    exact hframe
  have hout : execute (roundingProgram W B) D.graph (lambda,zeta) ids (objectiveInput D ids orig) =
      fun v => selectedLabel (D.labels v) (sequenceNums W B D ids orig k zeta u0 k v) := by
    funext v
    unfold execute SmoothedMIS.LocalAlg.output
    rw [roundingProgram_end]
    change selectedLabel
      ((foldRoundActions W D.graph (planPrefix W B k zeta k)
        (fun v => initialRoundData W lambda zeta (ids v) (objectiveInput D ids orig v)) v).input.labels)
      ((foldRoundActions W D.graph (planPrefix W B k zeta k)
        (fun v => initialRoundData W lambda zeta (ids v) (objectiveInput D ids orig v)) v).numerator) = _
    rw [he]
    rfl
  dsimp only
  rw [hout]
  exact sequence_value W B hColor D lambda hD ids hi orig zeta hc hgap

end PairwiseProof

-- Solutions/Sol_pairwise_core.lean
open FasterDistributedMatching.ApproximateMatching

theorem solution
    (W : Deterministic (ℕ × ℕ) DistributedRounding.WeightedInput ℕ) (B : ℕ)
    (hB : 0 < B)
    (hTime : ∀ Q zeta, 2 ≤ Q → W.program.rounds (Q,zeta) ≤ B*(Q+logStar zeta))
    (hColor : ∀ (N : ℕ) (H : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
      (weights : Fin N → ℕ → ℝ) (col : Fin N → ℕ) (Q zeta : ℕ),
      2 ≤ Q → Proper H zeta col →
      (∀ v u, 0 ≤ weights v (ids u)) →
      (∀ v u, weights v (ids u) = weights u (ids v)) →
      let out := execute W H (Q,zeta) ids (fun v => (weights v,col v))
      (∀ v, out v < B*Q) ∧
      (Q:ℝ)*DistributedRounding.monochromatic H (fun v u => weights v (ids u)) out ≤
        4*(∑ v, DistributedRounding.incident H (fun v u => weights v (ids u)) v)) :
    ∃ (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (C : ℝ), 0 < C ∧
      (∀ lambda zeta, 0 < lambda → lambda ≤ 1 / 2 →
        A.program.rounds (lambda,zeta) ≤ budget C
          ((logTwo (1 / lambda)) ^ 2 + logTwo (1 / lambda) * (logStar zeta : ℝ))) ∧
      ∀ (N : ℕ) (D : PairwiseInstance N) (lambda : ℝ) (zeta : ℕ)
        (col : Fin N → ℕ), ValidObjective D lambda → Proper D.graph zeta col →
        finiteExpectation D (utility D) - finiteExpectation D (cost D) ≥
          (1 / 2) * finiteExpectation D (utility D) →
        ∀ ids : Fin N → ℕ, Function.Injective ids →
          let s := execute A D.graph (lambda,zeta) ids (objectiveInput D ids col)
          (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
          utility D s - cost D s ≥
            (9 / 10) * (finiteExpectation D (utility D) - finiteExpectation D (cost D))  := by
  refine ⟨PairwiseProof.roundingProgram W B,10000000*((B:ℝ)+1),by positivity,?_,?_⟩
  · intro lambda zeta hl hu
    exact PairwiseProof.rounding_runtime W B hTime lambda zeta hl hu
  · intro N D lambda zeta col hD hc hgap ids hi
    exact PairwiseProof.rounding_correct W B hColor N D lambda zeta col hD hc hgap ids hi
